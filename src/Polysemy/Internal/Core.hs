{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE BangPatterns            #-}
{-# LANGUAGE CPP                     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE EmptyCase               #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PatternSynonyms         #-}
{-# LANGUAGE RoleAnnotations         #-}
{-# LANGUAGE StrictData              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns            #-}
{-# LANGUAGE MonoLocalBinds          #-}
{-# LANGUAGE QuantifiedConstraints   #-}

{-# OPTIONS_HADDOCK not-home #-}
module Polysemy.Internal.Core where

#if __GLASGOW_HASKELL__ < 808
import Control.Monad.Fail
#endif
import Data.Coerce
import Data.Primitive.Array
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fix
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Traversable
import Data.Type.Equality
import Polysemy.Internal.Reflection
import Data.Kind
import Polysemy.Embed.Type
import Polysemy.Fail.Type
import Polysemy.Internal.Fixpoint
import Polysemy.Internal.Kind
import Polysemy.Internal.Opaque
import Polysemy.Internal.NonDet
import Polysemy.Internal.Utils
import Polysemy.Internal.Membership
import Polysemy.Internal.RowTransformer
import Polysemy.Internal.Sing
import Control.Monad.ST
import Unsafe.Coerce
import GHC.Exts (considerAccessible)
import Polysemy.Internal.FList
-- import Data.Vector (Vector)
-- import qualified Data.Vector as V
-- import qualified Data.Vector.Mutable as MV
-- import qualified Data.Vector.Fusion.Bundle as B
-- import qualified Data.Vector.Generic as G
-- import qualified Data.Vector.Generic.Mutable as GM

-- $setup
-- >>> import Data.Function
-- >>> import Polysemy.State
-- >>> import Polysemy.Error

------------------------------------------------------------------------------
-- | The 'Sem' monad handles computations of arbitrary extensible effects.
-- A value of type @Sem r@ describes a program with the capabilities of
-- @r@. For best results, @r@ should always be kept polymorphic, but you can
-- add capabilities via the 'Polysemy.Member' constraint.
--
-- The value of the 'Sem' monad is that it allows you to write programs
-- against a set of effects without a predefined meaning, and provide that
-- meaning later. For example, unlike with mtl, you can decide to interpret an
-- 'Polysemy.Error.Error' effect traditionally as an 'Either', or instead
-- as (a significantly faster) 'IO' 'Control.Exception.Exception'. These
-- interpretations (and others that you might add) may be used interchangeably
-- without needing to write any newtypes or 'Monad' instances. The only
-- change needed to swap interpretations is to change a call from
-- 'Polysemy.Error.runError' to 'Polysemy.Error.errorToIOFinal'.
--
-- The effect stack @r@ can contain arbitrary other monads inside of it. These
-- monads are lifted into effects via the 'Embed' effect. Monadic values can be
-- lifted into a 'Sem' via 'embed'.
--
-- Higher-order actions of another monad can be lifted into higher-order actions
-- of 'Sem' via the 'Polysemy.Final' effect, which is more powerful
-- than 'Embed', but also less flexible to interpret.
--
-- A 'Sem' can be interpreted as a pure value (via 'run') or as any
-- traditional 'Monad' (via 'Polysemy.runM').
-- Each effect @E@ comes equipped with some interpreters of the form:
--
-- @
-- runE :: 'Sem' (E ': r) a -> 'Sem' r a
-- @
--
-- which is responsible for removing the effect @E@ from the effect stack. It
-- is the order in which you call the interpreters that determines the
-- monomorphic representation of the @r@ parameter.
--
-- Order of interpreters can be important - it determines behaviour of effects
-- that manipulate state or change control flow. For example, when
-- interpreting this action:
--
-- >>> :{
--   example :: Members '[State String, Error String] r => Sem r String
--   example = do
--     put "start"
--     let throwing, catching :: Members '[State String, Error String] r => Sem r String
--         throwing = do
--           modify (++"-throw")
--           throw "error"
--           get
--         catching = do
--           modify (++"-catch")
--           get
--     catch @String throwing (\ _ -> catching)
-- :}
--
-- when handling 'Polysemy.Error.Error' first, state is preserved after error
-- occurs:
--
-- >>> :{
--   example
--     & runError
--     & fmap (either id id)
--     & evalState ""
--     & runM
--     & (print =<<)
-- :}
-- "start-throw-catch"
--
-- while handling 'Polysemy.State.State' first discards state in such cases:
--
-- >>> :{
--   example
--     & evalState ""
--     & runError
--     & fmap (either id id)
--     & runM
--     & (print =<<)
-- :}
-- "start-catch"
--
-- A good rule of thumb is to handle effects which should have \"global\"
-- behaviour over other effects later in the chain.
--
-- After all of your effects are handled, you'll be left with either
-- a @'Sem' '[] a@, a @'Sem' '[ 'Embed' m ] a@, or a @'Sem' '[ 'Polysemy.Final' m ] a@
-- value, which can be consumed respectively by 'run', 'runM', and
-- 'Polysemy.runFinal'.
--
-- ==== Examples
--
-- As an example of keeping @r@ polymorphic, we can consider the type
--
-- @
-- 'Member' ('Polysemy.State.State' String) r => 'Sem' r ()
-- @
--
-- to be a program with access to
--
-- @
-- 'Polysemy.State.get' :: 'Sem' r String
-- 'Polysemy.State.put' :: String -> 'Sem' r ()
-- @
--
-- methods.
--
-- By also adding a
--
-- @
-- 'Member' ('Polysemy.Error' Bool) r
-- @
--
-- constraint on @r@, we gain access to the
--
-- @
-- 'Polysemy.Error.throw' :: Bool -> 'Sem' r a
-- 'Polysemy.Error.catch' :: 'Sem' r a -> (Bool -> 'Sem' r a) -> 'Sem' r a
-- @
--
-- functions as well.
--
-- In this sense, a @'Member' ('Polysemy.State.State' s) r@ constraint is
-- analogous to mtl's @'Control.Monad.State.Class.MonadState' s m@ and should
-- be thought of as such. However, /unlike/ mtl, a 'Sem' monad may have
-- an arbitrary number of the same effect.
--
-- For example, we can write a 'Sem' program which can output either
-- 'Int's or 'Bool's:
--
-- @
-- foo :: ( 'Member' ('Polysemy.Output.Output' Int) r
--        , 'Member' ('Polysemy.Output.Output' Bool) r
--        )
--     => 'Sem' r ()
-- foo = do
--   'Polysemy.Output.output' @Int  5
--   'Polysemy.Output.output' True
-- @
--
-- Notice that we must use @-XTypeApplications@ to specify that we'd like to
-- use the ('Polysemy.Output.Output' 'Int') effect.
--
-- @since 0.1.2.0
newtype Sem (r :: EffectRow) a = Sem {
    runSem :: ∀ res. Handlers r (Sem r) res -> (a -> res) -> res
  }

data Handlers r m res where
  Handlers :: (forall x. m x -> z x)
           -> {-# UNPACK #-} !(HandlerVector r z res)
           -> Handlers r m res

emptyHandlers :: Handlers '[] m res
emptyHandlers = Handlers id (HandlerVector emptySV)
{-# INLINE emptyHandlers #-}


emptyHandlers' :: HandlerVector '[] m res
emptyHandlers' = HandlerVector emptySV
{-# INLINE emptyHandlers' #-}

-- expensive
getHandlerVector :: Handlers r m res -> HandlerVector r m res
getHandlerVector (Handlers n (HandlerVector hs)) = HandlerVector $
  fmap (\(Handler' h) -> Handler' $ \wav -> h (hoistWeaving n wav)) hs
{-# INLINE getHandlerVector #-}

imapHandlers' :: (   forall e x
                   . ElemOf e r
                  -> (forall y. Weaving e m y -> (y -> res) -> res)
                  -> Weaving e m' x -> (x -> res') -> res'
                )
              -> HandlerVector r m res -> HandlerVector r m' res'
imapHandlers' f (HandlerVector hs) = HandlerVector $
  imapSV (\i (Handler' h) -> Handler' (f (UnsafeMkElemOf i) h)) hs

hoistHandler :: (forall x. m x -> n x)
             -> (forall x. Weaving e n x -> (x -> res) -> res)
             -> (forall x. Weaving e m x -> (x -> res) -> res)
hoistHandler n f = \wav -> f (hoistWeaving n wav)
{-# INLINE hoistHandler #-}

imapHandlers :: (   forall e x
                  . ElemOf e r
                 -> (forall y. Weaving e m y -> (y -> res) -> res)
                 -> Weaving e m' x -> (x -> res') -> res'
               )
             -> Handlers r m res -> HandlerVector r m' res'
imapHandlers f (Handlers n (HandlerVector hs)) = HandlerVector $
  imapSV (\i (Handler' h) ->
    Handler' (f (UnsafeMkElemOf i) (\wv -> h (hoistWeaving n wv))))
    hs
{-# INLINE imapHandlers #-}

{-
Best of both worlds is probably a hybrid between FList and Vector.
Or FList with intermittent memoization.
Or both.

When operations reaches some threshold compared to the length of the list. Like,
say, 1.5 times greater than the length of the list
_or_ ops reaches a cap of... 1000?
memoizeFList resets operations to 0
-}

-- data BestList a = BestList {-# UNPACK #-} !(Vector a) {-# UNPACK #-} !(FList a)

mapHandlers' :: (   forall e x
                   . (forall y. Weaving e m y -> (y -> res) -> res)
                  -> Weaving e m' x -> (x -> res') -> res'
                )
              -> HandlerVector r m res -> HandlerVector r m' res'
mapHandlers' f (HandlerVector hs) = HandlerVector $
  fmap (\(Handler' h) -> Handler' (f h)) hs
{-# INLINE mapHandlers' #-}

mapHandlers :: (   forall e x
                 . (forall y. Weaving e m y -> (y -> res) -> res)
                -> Weaving e m' x -> (x -> res') -> res'
              )
            -> Handlers r m res -> HandlerVector r m' res'
mapHandlers f (Handlers n (HandlerVector hs)) = HandlerVector $
  fmap (\(Handler' h) -> Handler' (f (\wv -> h (hoistWeaving n wv)))) hs
{-# INLINE mapHandlers #-}

mkHandlers :: HandlerVector r m res -> Handlers r m res
mkHandlers = Handlers id
{-# INLINE mkHandlers #-}

type Handler e m res = forall x. Weaving e m x -> (x -> res) -> res

newtype Handler' m res = Handler' { unHandler' :: forall e. Handler e m res }

type role HandlerVector representational representational representational
newtype HandlerVector (r :: EffectRow) m res = HandlerVector (SmallVector (Handler' m res))

{-

Complexity...
We want SmallArrays.

Invariant = ops <= 20 || (ops <= 1000 && ops < 2 * n + 10)

indexing = O(ops)
cons = O(1)
concatenation = O(1)
fmap = O(1)
gen = O(1)
update = O(1)

data FList a = FList {-# UNPACK #-} !(Vector a) {-# UNPACK #-} !Int {-# UNPACK #-} !Int (Int -> a)


-}


getHandler :: Handlers r m res -> ElemOf e r -> Handler e m res
getHandler (Handlers to v) pr =
  let
    !h = getHandler' v pr
  in
    \wav -> h (hoistWeaving to wav)
{-# INLINE getHandler #-}

getHandler' :: HandlerVector r m res -> ElemOf e r -> Handler e m res
getHandler' (HandlerVector v) (UnsafeMkElemOf i) = unHandler' (indexSV v i)
{-# INLINE getHandler' #-}

-- lupdate :: Int -> a -> [a] -> [a]
-- lupdate 0 a (_:xs) = a:xs
-- lupdate !i a (x:xs) = x : lupdate (i - 1) a xs
-- lupdate !_ _ _ = []

infixr 5 `concatHandlers'`
concatHandlers' :: HandlerVector l m res
                -> HandlerVector r m res
                -> HandlerVector (Append l r) m res
concatHandlers' (HandlerVector l) (HandlerVector r) = HandlerVector (l `concatSV` r)
{-# INLINE concatHandlers' #-}

generateHandlers'
  :: SList r
  -> (forall e x. ElemOf e r -> Weaving e m x -> (x -> res) -> res)
  -> HandlerVector r m res
generateHandlers' (UnsafeMkSList s) f =
  HandlerVector (generateSV s (unsafeCoerce f))
{-# INLINE generateHandlers' #-}

replaceHandler' :: forall r e_ e l m res
                . SList l
               -> Handler e m res
               -> HandlerVector (Append l (e_ ': r)) m res
               -> HandlerVector (Append l (e ': r)) m res
replaceHandler' (UnsafeMkSList i) h (HandlerVector v) =
  HandlerVector $ updateSV i (unsafeCoerce h) v
{-# INLINE replaceHandler' #-}

interceptHandler' :: forall r e m res
                   . ElemOf e r
                  -> Handler e m res
                  -> HandlerVector r m res
                  -> HandlerVector r m res
interceptHandler' (UnsafeMkElemOf i) h (HandlerVector v) =
  HandlerVector $ updateSV i (unsafeCoerce h) v
{-# INLINE interceptHandler' #-}

infixr 5 `consHandler'`
consHandler' :: Handler e m res
             -> HandlerVector r m res
             -> HandlerVector (e ': r) m res
consHandler' h (HandlerVector hs) = HandlerVector (unsafeCoerce h `consSV` hs)
{-# INLINE consHandler' #-}

dropHandlers' :: forall l r m res
               . KnownList l
              => HandlerVector (Append l r) m res
              -> HandlerVector r m res
dropHandlers' (HandlerVector hs) | UnsafeMkSList l <- singList @l =
  HandlerVector (dropSV l hs)
{-# INLINE dropHandlers' #-}

takeHandlers' :: forall l r m res
               . KnownList l
              => HandlerVector (Append l r) m res
              -> HandlerVector l m res
takeHandlers' (HandlerVector hs) | UnsafeMkSList l <- singList @l =
  HandlerVector (takeSV l hs)
{-# INLINE takeHandlers' #-}

splitHandlers' :: forall l r m res
                . KnownList l
               => HandlerVector (Append l r) m res
               -> (HandlerVector l m res, HandlerVector r m res)
splitHandlers' (HandlerVector hs)
  | UnsafeMkSList n <- singList @l, (l, r) <- splitSV n hs =
      (HandlerVector l, HandlerVector r)

transformHandlerVector
  :: RowTransformer r r'
  -> (forall m res. HandlerVector r' m res -> HandlerVector r m res)
transformHandlerVector t0 = \(HandlerVector v) -> HandlerVector (t0' v)
  where
    !t0' = go t0

    go :: RowTransformer r r'
       -> SmallVector (Handler' m res) -> SmallVector (Handler' m res)
    go Id = id
    go (Join l r) =
      let
        !l' = go l
        !r' = go r
      in
        r' . l'
    go (Raise (UnsafeMkSList n)) = dropSV n
    go (Extend (UnsafeMkSList n)) = dropEndSV n
    go (ExtendAlt _ (UnsafeMkSList n)) = takeSV n
    go (Under (UnsafeMkSList n) t) =
      let
        !t' = go t
      in
        \v -> case splitSV n v of
          (l, r) ->  l `concatSV` t' r
    go (Subsume (UnsafeMkElemOf pr)) = \v ->
      let
        !h = v `indexSV` pr
      in
        h `consSV` v
    go (Expose (UnsafeMkElemOf pr)) = \v -> case unconsSV v of
      (!h, v') -> updateSV pr h v'
    go (Swap _ (UnsafeMkSList l) (UnsafeMkSList m)) = \v ->
      case splitSV m v of
        (mv, lrv) | (lv, rv) <- splitSV l lrv ->
          lv `concatSV` mv `concatSV` rv
    go (Split _ f g) =
      let
        !f' = go f
        !g' = go g
      in
        \v -> f' v `concatSV` g' v

------------------------------------------------------------------------------
-- | Rewrite the effect stack of a 'Sem' using with an explicit row transformer
transformSem :: forall r' r
              . RowTransformer r r' -> (forall x. Sem r x -> Sem r' x)
transformSem Id = id
transformSem t = go
  where
    t' :: forall m res. HandlerVector r' m res -> HandlerVector r m res
    !t' = transformHandlerVector t

    go :: forall x. Sem r x -> Sem r' x
    go = hoistSem $ \(Handlers n hs) -> Handlers (n . go_) (t' hs)
    {-# INLINE go #-}

    go_ :: forall x. Sem r x -> Sem r' x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE[1] transformSem #-}

{-# RULES
"transformSem/transformSem"
  forall f g m.
    transformSem f (transformSem g m) = transformSem (joinRow f g) m
#-}

------------------------------------------------------------------------------
-- | Like 'runSem' but arguments rearranged for better ergonomics sometimes.
usingSem
    :: (a -> res)
    -> Handlers r (Sem r) res
    -> Sem r a
    -> res
usingSem c k m = runSem m k c
{-# INLINE usingSem #-}

------------------------------------------------------------------------------
-- | Extend the stack of a 'Sem' with an explicit 'Handlers' transformation.
hoistSem
  :: forall r' r
   . (forall res. Handlers r' (Sem r') res -> Handlers r (Sem r) res)
  -> (forall x. Sem r x -> Sem r' x)
hoistSem n = \sem -> Sem $ \k c ->
  let
    !k' = n k
  in
    runSem sem k' c
{-# INLINE hoistSem #-}

interpretViaHandlerFast
  :: forall e r
   . (   forall z x res
       . (forall y. Sem r y -> z y)
      -> HandlerVector r z res
      -> Weaving e z x -> (x -> res) -> res
     )
  -> InterpreterFor e r
interpretViaHandlerFast h = go
  where
    go :: InterpreterFor e r
    go = hoistSem $ \(Handlers n v) ->
      let
        AHandler !ah = AHandler (h n v)
      in
        Handlers (n . go_) (consHandler' ah v)
    {-# INLINE go #-}

    go_ :: InterpreterFor e r
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE interpretViaHandlerFast #-}

reinterpretViaHandlerFast
  :: forall e1 e2 r
   . (   forall z x res
       . (forall y. Sem (e2 ': r) y -> z y)
      -> HandlerVector (e2 ': r) z res
      -> Weaving e1 z x -> (x -> res) -> res
     )
  -> (forall x. Sem (e1 ': r) x -> Sem (e2 ': r) x)
reinterpretViaHandlerFast h = go
  where
    go :: forall x. Sem (e1 ': r) x -> Sem (e2 ': r) x
    go = hoistSem $ \(Handlers n v) ->
      let
        AHandler !ah = AHandler (h n v)
      in
        Handlers (n . go_) (consHandler' ah (dropHandlers' @'[_] v))
    {-# INLINE go #-}

    go_ :: forall x. Sem (e1 ': r) x -> Sem (e2 ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE reinterpretViaHandlerFast #-}

interpretViaHandlerSlow
  :: forall e r
   . (   forall x res
       . Handlers r (Sem r) res
      -> Weaving e (Sem (e ': r)) x -> (x -> res) -> res
     )
  -> InterpreterFor e r
interpretViaHandlerSlow h = go
  where
    go :: InterpreterFor e r
    go = hoistSem $ \hs ->
      let
        AHandler !ah = AHandler (h hs)
      in
        mkHandlers $ consHandler' ah (hoistHandlers' go_ hs)
    {-# INLINE go #-}

    go_ :: InterpreterFor e r
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE interpretViaHandlerSlow #-}

hoistHandlers :: (forall x. m x -> n x) -> Handlers r n res -> Handlers r m res
hoistHandlers n (Handlers n' hs) = Handlers (n' . n) hs
{-# INLINE hoistHandlers #-}

hoistHandlers' :: (forall x. m x -> n x)
               -> Handlers r n res -> HandlerVector r m res
hoistHandlers' n = getHandlerVector . hoistHandlers n
{-# INLINE hoistHandlers' #-}

instance Functor (Sem f) where
  fmap f m = Sem $ \k c -> runSem m k (c . f)
  {-# INLINE fmap #-}

instance Applicative (Sem f) where
  pure a = Sem $ \_ c -> c a
  {-# INLINE pure #-}

  ma <*> mb = Sem $ \k c -> runSem ma k (\f -> runSem mb k (c . f))
  {-# INLINE (<*>) #-}

  liftA2 f ma mb = Sem $ \k c -> runSem ma k (\a -> runSem mb k (c . f a))
  {-# INLINE liftA2 #-}

  ma <* mb = Sem $ \k c -> runSem ma k (\a -> runSem mb k (\_ -> c a))
  {-# INLINE (<*) #-}

  ma *> mb = Sem $ \k c -> runSem ma k (\_ -> runSem mb k c)
  {-# INLINE (*>) #-}

instance Monad (Sem f) where
  ma >>= f = Sem $ \k c -> runSem ma k (\a -> runSem (f a) k c)
  {-# INLINE (>>=) #-}


instance (Member NonDet r) => Alternative (Sem r) where
  empty = send Empty
  {-# INLINE empty #-}
  a <|> b = send (Choose a b)
  {-# INLINE (<|>) #-}

-- | @since 0.2.1.0
instance (Member NonDet r) => MonadPlus (Sem r) where
  mzero = empty
  mplus = (<|>)

-- | @since 1.1.0.0
instance (Member Fail r) => MonadFail (Sem r) where
  fail = send .# Fail
  {-# INLINE fail #-}

-- | @since 1.6.0.0
instance Semigroup a => Semigroup (Sem f a) where
  (<>) = liftA2 (<>)

-- | @since 1.6.0.0
instance Monoid a => Monoid (Sem f a) where
  mempty = pure mempty

------------------------------------------------------------------------------
-- | This instance will only lift 'IO' actions. If you want to lift into some
-- other 'MonadIO' type, use this instance, and handle it via the
-- 'Polysemy.IO.embedToMonadIO' interpretation.
instance Member (Embed IO) r => MonadIO (Sem r) where
  liftIO = embed
  {-# INLINE liftIO #-}

instance Member Fixpoint r => MonadFix (Sem r) where
  mfix f = send $ Fixpoint f
  {-# INLINE mfix #-}

data Weave t r m a where
  RestoreW  :: t a -> Weave t r m a
  GetStateW :: ((forall x. x -> t x) -> a) -> Weave t r m a
  LiftWithW :: ((forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x)) -> a)
            -> Weave t r m a
  EmbedW    :: Sem r a -> Weave t r m a

newtype Traversal t = Traversal {
    getTraversal :: forall f a b. Applicative f => (a -> f b) -> t a -> f (t b)
  }

newtype ViaTraversal (s :: Type) t (a :: Type) =
  ViaTraversal { getViaTraversal :: t a }

instance Reifies s (Traversal t) => Functor (ViaTraversal s t) where
  fmap = fmapDefault
  {-# INLINE fmap #-}

instance Reifies s (Traversal t) => Foldable (ViaTraversal s t) where
  foldMap = foldMapDefault
  {-# INLINE foldMap #-}

instance Reifies s (Traversal t) => Traversable (ViaTraversal s t) where
  traverse f (ViaTraversal t) = ViaTraversal <$> getTraversal (reflect @s) f t
  {-# INLINE traverse #-}

------------------------------------------------------------------------------
-- | An extensible, type-safe union. The @r@ type parameter is a type-level
-- list of effects, any one of which may be held within the 'Union'.
data Union (r :: EffectRow) (mWoven :: Type -> Type) a where
  Union
      :: -- A proof that the effect is actually in @r@.
         {-# UNPACK #-} !(ElemOf e r)
         -- The effect to wrap. The functions 'prj' and 'decomp' can help
         -- retrieve this value later.
      -> !(Weaving e m a)
      -> Union r m a

------------------------------------------------------------------------------
-- | Decompose a 'Union'. Either this union contains an effect @e@---the head
-- of the @r@ list---or it doesn't.
decomp :: Union (e ': r) m a -> Either (Union r m a) (Weaving e m a)
decomp (Union p a) =
  case p of
    Here  -> Right a
    There pr -> Left $ Union pr a
{-# INLINABLE decomp #-}

------------------------------------------------------------------------------
-- | Polysemy's core type that stores effect values together with information
-- about the higher-order interpretation state of its construction site.
data Weaving e m a where
  Sent :: e z a -> (forall x. z x -> m x) -> Weaving e m a
  Weaved
    :: forall t e z a resultType m.
       (Coercible (t a) resultType,
        forall x y. Coercible x y => Coercible (t x) (t y))
    => { weaveEffect :: e z a
       -- ^ The original effect GADT originally lifted via
       -- a variant of 'Polysemy.Internal.send'.
       -- ^ @z@ is usually @Sem rInitial@, where @rInitial@ is the effect row
       -- that was in scope when this 'Weaving' was originally created.
       , traverseState :: Traversal t
       -- ^ An implementation of 'traverse' for @t@.
       , weaveInitState :: forall x. x -> t x
       -- ^ A piece of state that other effects' interpreters have already
       -- woven through this 'Weaving'.
       , weaveDistrib :: forall x. t (z x) -> m (t x)
       -- ^ Distribute @t@ by transforming @into @m@. This is
       -- usually of the form @t ('Polysemy.Sem' (Some ': Effects ': r) x) ->
       --   Sem r (t x)@
       , weaveLowering :: forall r x. Sem (Weave t r ': r) x -> Sem r (t x)
       -- TODO document this
       } -> Weaving e m resultType

fromFOEff :: Weaving e m a
          -> (forall z b. (b -> a) -> e z b -> res)
          -> res
fromFOEff w c = case w of
  Sent e _ -> c id e
  Weaved e _ mkS _ _ -> c (coerce #. mkS) e
{-# INLINEABLE fromFOEff #-}
-- {-# INLINE fromFOEff #-}

fromSimpleHOEff :: Weaving e (Sem r) a
                -> (   forall z t b
                     . (forall x. x -> t x)
                    -> (forall x. z x -> Sem r (t x))
                    -> (t b -> a)
                    -> e z b
                    -> res
                   )
                -> res
fromSimpleHOEff w c = case w of
  Sent e n -> c Identity (fmap Identity #. n) runIdentity e
  Weaved e _ mkS wv _ -> c mkS (wv . mkS) coerce e
{-# INLINEABLE fromSimpleHOEff #-}
-- {-# INLINE fromSimpleHOEff #-}

hoist :: (∀ x. m x -> n x)
      -> Union r m a
      -> Union r n a
hoist n' (Union w wav) = Union w (hoistWeaving n' wav)
{-# INLINEABLE hoist #-}
-- {-# INLINE hoist #-}

hoistWeaving :: (∀ x. m x -> n x)
             -> Weaving e m a
             -> Weaving e n a
hoistWeaving n' = \case
  Sent e n -> Sent e (n' . n)
  Weaved e trav mkS wv lwr -> Weaved e trav mkS (n' . wv) lwr
{-# INLINE hoistWeaving #-}

newtype AHandler e m res = AHandler (Handler e m res)

rewriteComposeWeave :: Sem (Weave (Compose t t') r ': r) x
                    -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
rewriteComposeWeave = go
  where
    go :: forall t t' r x
        . Sem (Weave (Compose t t') r ': r) x
       -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
    go = hoistSem $ \(Handlers n hs) ->
      let
        AHandler !ht' = AHandler $ getHandler' hs Here
        AHandler !ht = AHandler $ getHandler' hs (There Here)
        AHandler h = AHandler $ \wav c -> fromFOEff wav $ \ex -> \case
          RestoreW (Compose tt') ->
            ht (mkW $ RestoreW tt') \t' ->
            ht' (mkW $ RestoreW t') (c . ex)
          GetStateW main ->
            (`ht` id) $ mkW $ GetStateW $ \mkS ->
            (`ht'` c) $ mkW $ GetStateW $ \mkS' ->
            ex $ main $ Compose #. mkS . mkS'
          LiftWithW main ->
            (`ht` id) $ mkW $ LiftWithW \lwr ->
            (`ht'` c) $ mkW $ LiftWithW \lwr' ->
            ex $ main (fmap Compose #. lwr . lwr' . go_)
          EmbedW m ->
            ht' (mkW $ EmbedW (sendUsing Here (EmbedW m))) (c . ex)
      in
        Handlers (n . go_) $ consHandler' h (dropHandlers' @'[_, _] hs)
    {-# INLINE go #-}

    go_ :: Sem (Weave (Compose t t') r ': r) x
        -> Sem (Weave t' (Weave t r ': r) ': Weave t r ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE rewriteComposeWeave #-}
-- {-# INLINE rewriteComposeWeave #-}

class    (forall x y. Coercible x y => Coercible (t x) (t y))
      => Representational1 t
instance (forall x y. Coercible x y => Coercible (t x) (t y))
      => Representational1 t

weave :: (Traversable t, Representational1 n, Representational1 t)
      => t ()
      -> (forall x. t (m x) -> n (t x))
      -> (forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x))
      -> Weaving e m a
      -> Weaving e n (t a)
weave s' wv' lwr' = \case
  Sent e n -> Weaved e (Traversal traverse) (<$ s') (wv' . fmap n) lwr'
  Weaved e (Traversal trav) mkS wv lwr ->
    let
      cTrav = Traversal (\f -> fmap Compose . traverse (trav f) .# getCompose)
    in
      Weaved
        e
        cTrav
        (\x -> Compose $ mkS x <$ s')
        (coerce #. wv' . fmap wv .# getCompose)
        (fmap Compose #. lwr' . lwr . rewriteComposeWeave)
{-# INLINABLE weave #-}
{-# SPECIALIZE INLINE
  weave :: (Traversable t, Representational1 t)
        => t ()
        -> (forall x. t (m x) -> Sem r'' (t x))
        -> (forall r' x. Sem (Weave t r' ': r') x -> Sem r' (t x))
        -> Weaving e m a -> Weaving e (Sem r'') (t a)
  #-}


rewriteWeaving :: (∀ z x. e z x -> e' z x)
               -> Weaving e m a
               -> Weaving e' m a
rewriteWeaving t = \case
  Sent e n -> Sent (t e) n
  Weaved e trav mkS wv lwr -> Weaved (t e) trav mkS wv lwr
{-# INLINEABLE rewriteWeaving #-}

------------------------------------------------------------------------------
-- | An effect for collecting multiple effects into one effect.
--
-- Useful for effect newtypes -- effects defined through creating a newtype
-- over an existing effect, and then defining actions and interpretations on
-- the newtype by using 'Polysemy.rewrite' and 'Polysemy.transform'.
--
-- By making a newtype of 'Polysemy.Bundle.Bundle', it's possible to wrap
-- multiple effects in one newtype.
data Bundle r m a where
  Bundle :: {-# UNPACK #-} !(ElemOf e r) -> e m a -> Bundle r m a

rewriteWeaving' :: (∀ z x. e z x -> Bundle r z x)
                -> Weaving e m a
                -> Union r m a
rewriteWeaving' t = \case
  Sent e n
    | Bundle pr e' <- t e -> Union pr (Sent e' n)
  Weaved e trav mkS wv lwr
    | Bundle pr e' <- t e -> Union pr (Weaved e' trav mkS wv lwr)
{-# INLINEABLE rewriteWeaving' #-}
-- {-# INLINE rewriteWeaving #-}

------------------------------------------------------------------------------
-- | Create a @Weaving e m a@ from an @e m a@
-- transformation to transform the monad.
mkW :: forall e m a. e m a -> Weaving e m a
mkW e = Sent e id
{-# INLINE mkW #-}

mkWVia :: forall e z m a. (forall x. z x -> m x) -> e z a -> Weaving e m a
mkWVia n e = Sent e n
{-# INLINE mkWVia #-}
-- {-# INLINE injVia #-}

------------------------------------------------------------------------------
-- | Execute an action of an effect.
--
-- This is primarily used to create methods for actions of effects:
--
-- @
-- data FooBar m a where
--   Foo :: String -> m a -> FooBar m a
--   Bar :: FooBar m Int
--
-- foo :: Member FooBar r => String -> Sem r a -> Sem r a
-- foo s m = send (Foo s m)
--
-- bar :: Member FooBar r => Sem r Int
-- bar = send Bar
-- @
--
-- 'Polysemy.makeSem' allows you to eliminate this boilerplate.
send :: Member e r => e (Sem r) a -> Sem r a
send = liftWeaving membership . mkW
-- {-# INLINE[3] send #-}
{-# INLINEABLE[3] send #-}

------------------------------------------------------------------------------
-- | Execute an action of an effect, given a natural transformation from
-- the monad used for the higher-order chunks in the effect to
-- @'Polysemy.Sem' r@.
--
-- @since 2.0.0.0
sendVia :: forall e z r a
         . Member e r
        => (forall x. z x -> Sem r x)
        -> e z a -> Sem r a
sendVia n = liftWeaving membership . mkWVia n
-- {-# INLINE[3] sendVia #-}
{-# INLINEABLE[3] sendVia #-}

------------------------------------------------------------------------------
-- | Embed an effect into a 'Sem', given an explicit proof
-- that the effect exists in @r@.
--
-- This is useful in conjunction with 'Polysemy.Membership.tryMembership',
-- in order to conditionally make use of effects.
sendUsing :: ElemOf e r -> e (Sem r) a -> Sem r a
sendUsing pr = liftWeaving pr . mkW
-- {-# INLINE[3] sendUsing #-}
{-# INLINEABLE[3] sendUsing #-}

------------------------------------------------------------------------------
-- | Embed an effect into a 'Sem', given an explicit proof
-- that the effect exists in @r@, and a natural transformation from the monad
-- used for the higher-order thunks in the effect to @'Polysemy.Sem' r@.
sendViaUsing :: ElemOf e r -> (forall x. z x -> Sem r x) -> e z a -> Sem r a
sendViaUsing pr n = liftWeaving pr . mkWVia n
-- {-# INLINE[3] sendViaUsing #-}
{-# INLINEABLE[3] sendViaUsing #-}


------------------------------------------------------------------------------
-- | Embed a monadic action @m@ in 'Sem'.
--
-- @since 1.0.0.0
embed :: Member (Embed m) r => m a -> Sem r a
embed = send .# Embed
{-# INLINEABLE embed #-}
-- {-# INLINE embed #-}

------------------------------------------------------------------------------
-- | Create a @'Sem' r@ from a @'Weaving' e ('Sem' r)@ given a proof that @e@ is
-- is a member of @r@
liftWeaving :: ElemOf e r -> Weaving e (Sem r) a -> Sem r a
liftWeaving pr wav = Sem $ \k -> getHandler k pr wav
{-# INLINEABLE liftWeaving #-}
-- {-# INLINE liftSem #-}

------------------------------------------------------------------------------
-- | Type synonym for interpreters that consume an effect without changing the
-- return value. Offered for user convenience.
--
-- @r@ Is kept polymorphic so it's possible to place constraints upon it:
--
-- @
-- teletypeToIO :: 'Member' (Embed IO) r
--              => 'InterpreterFor' Teletype r
-- @
type InterpreterFor e r = ∀ a. Sem (e ': r) a -> Sem r a
