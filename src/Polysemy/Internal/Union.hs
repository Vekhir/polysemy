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
{-# LANGUAGE QuantifiedConstraints   #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_HADDOCK not-home, prune #-}

-- | Description: 'Union', 'Weaving' and 'ElemOf', Polysemy's core types
module Polysemy.Internal.Union
  ( Union (..)
  , Weaving (..)
  , fromFOEff
  , rewriteWeaving
  , Member
  , weave
  , liftHandler
  , liftHandlerWithNat
  , weaveToTransWeave
  , hoist

  -- * Building Unions
  , inj
  , injUsing
  , injWeaving
  , weaken

  -- * Using Unions
  , decomp
  , prj
  , prjUsing
  , extract
  , absurdU
  , decompCoerce
  -- * Witnesses
  , ElemOf (.., Here, There)
  , membership
  , sameMember
  -- * Checking membership
  , KnownRow
  , tryMembership

  -- * Membership manipulation
  , idMembership
  , splitMembership
  , extendMembershipLeft
  , extendMembershipRight
  , injectMembership
  , absurdMembership
  , weakenList
  , weakenMid

  , module Polysemy.Internal.WeaveClass

  ) where

import Data.Coerce
import Data.Functor.Identity
import Data.Typeable
import Control.Monad.Trans
import Polysemy.Internal.Kind
import Polysemy.Internal.WeaveClass
import Polysemy.Internal.Core
import Polysemy.Internal.Sing (SList (..))


weaveToTransWeave :: MonadTransWeave t
                  => Sem (Weave (StT t) r ': r) a -> t (Sem r) a
weaveToTransWeave = usingSem return $ \u c -> case decomp u of
  Left g -> liftHandlerWithNat weaveToTransWeave liftSem g >>= c
  Right wav -> fromFOEff wav $ \ex -> \case
    RestoreW t -> restoreT (return t) >>= c . ex
    GetStateW main -> (>>= c . ex) $ liftWith $ \lwr ->
      return $ main (\x -> runIdentity (lwr (return x)))
    LiftWithW main -> (>>= c . ex) $ liftWith $ \lwr ->
      return $ main (lwr . weaveToTransWeave)
    EmbedW m -> lift m >>= (c . ex)

-- Not used (nearly as much) anymore
liftHandler :: ( MonadTransWeave t, Monad m, Monad n
               , forall x y. Coercible x y => Coercible (m x) (m y))
            => (forall x. Union r m x -> n x)
            -> Union r (t m) a -> t n a
liftHandler = liftHandlerWithNat id
{-# INLINE liftHandler #-}

liftHandlerWithNat :: (MonadTransWeave t, Monad m, Monad n
                      , forall x y. Coercible x y => Coercible (m x) (m y))
                   => (forall x. q x -> t m x)
                   -> (forall x. Union r m x -> n x)
                   -> Union r q a -> t n a
liftHandlerWithNat n handler u = controlT $ \lower -> do
  initS <- lower (return ())
  handler $
    weave
      initS
      (\t -> lower (restoreT (return t) >>= n))
      (lower . weaveToTransWeave)
      u
{-# INLINE liftHandlerWithNat #-}

------------------------------------------------------------------------------
-- | A class for effect rows whose elements are inspectable.
--
-- This constraint is eventually satisfied as @r@ is instantied to a
-- monomorphic list.
-- (E.g when @r@ becomes something like
-- @'['Polysemy.State.State' Int, 'Polysemy.Output.Output' String, 'Polysemy.Embed' IO]@)
class KnownRow r where
  tryMembership' :: forall e. Typeable e => Maybe (ElemOf e r)

instance KnownRow '[] where
  tryMembership' = Nothing
  {-# INLINABLE tryMembership' #-}

instance (Typeable e, KnownRow r) => KnownRow (e ': r) where
  tryMembership' :: forall e'. Typeable e' => Maybe (ElemOf e' (e ': r))
  tryMembership' = case eqT @e @e' of
    Just Refl -> Just Here
    _         -> There <$> tryMembership' @r @e'
  {-# INLINABLE tryMembership' #-}

------------------------------------------------------------------------------
-- | Extracts a proof that @e@ is an element of @r@ if that
-- is indeed the case; otherwise returns @Nothing@.
tryMembership :: forall e r. (Typeable e, KnownRow r) => Maybe (ElemOf e r)
tryMembership = tryMembership' @r @e
{-# INLINABLE tryMembership #-}


------------------------------------------------------------------------------
-- | Extends a proof that @e@ is an element of @r@ to a proof that @e@ is an
-- element of the concatenation of the lists @l@ and @r@.
-- @l@ must be specified as a singleton list proof.
extendMembershipLeft :: forall r l e
                      . SList l -> ElemOf e r -> ElemOf e (Append l r)
extendMembershipLeft (UnsafeMkSList n) (UnsafeMkElemOf pr) =
  UnsafeMkElemOf (n + pr)
{-# INLINABLE extendMembershipLeft #-}


------------------------------------------------------------------------------
-- | Extends a proof that @e@ is an element of @l@ to a proof that @e@ is an
-- element of the concatenation of the lists @l@ and @r@.
extendMembershipRight :: forall l r e. ElemOf e l -> ElemOf e (Append l r)
extendMembershipRight (UnsafeMkElemOf pr) = (UnsafeMkElemOf pr)
{-# INLINABLE extendMembershipRight #-}


------------------------------------------------------------------------------
-- | Extends a proof that @e@ is an element of @left <> right@ to a proof that
-- @e@ is an element of @left <> mid <> right@.
-- Both @left@ and @right@ must be specified as singleton list proofs.
injectMembership :: forall right e left mid
                  . SList left
                 -> SList mid
                 -> ElemOf e (Append left right)
                 -> ElemOf e (Append left (Append mid right))
injectMembership (UnsafeMkSList l) (UnsafeMkSList m) (UnsafeMkElemOf pr)
  | pr < l    = UnsafeMkElemOf pr
  | otherwise = UnsafeMkElemOf (m + pr)
{-# INLINABLE injectMembership #-}

splitMembership :: forall right left e
                 . SList left
                -> ElemOf e (Append left right)
                -> Either (ElemOf e left) (ElemOf e right)
splitMembership (UnsafeMkSList l) (UnsafeMkElemOf pr)
  | pr < l    = Left (UnsafeMkElemOf pr)
  | otherwise = Right $! UnsafeMkElemOf (pr - l)

-- | A variant of id that gets inlined late for rewrite rule purposes
idMembership :: ElemOf (e :: Effect) r -> ElemOf e r
idMembership = id
{-# INLINE[0] idMembership #-}

------------------------------------------------------------------------------
-- | Retrieve the last effect in a 'Union'.
extract :: Union '[e] m a -> Weaving e m a
extract (Union Here a)   = a
extract (Union (There pr) _) = case pr of {}
{-# INLINABLE extract #-}


------------------------------------------------------------------------------
-- | An empty union contains nothing, so this function is uncallable.
absurdU :: Union '[] m a -> b
absurdU (Union pr _) = absurdMembership pr


------------------------------------------------------------------------------
-- | Weaken a 'Union' so it is capable of storing a new sort of effect at the
-- head.
weaken :: forall e r m a. Union r m a -> Union (e ': r) m a
weaken (Union pr a) = Union (There pr) a
{-# INLINABLE weaken #-}


------------------------------------------------------------------------------
-- | Weaken a 'Union' so it is capable of storing a number of new effects at
-- the head, specified as a singleton list proof.
weakenList :: SList l -> Union r m a -> Union (Append l r) m a
weakenList sl (Union pr e) = Union (extendMembershipLeft sl pr) e
{-# INLINABLE weakenList #-}


------------------------------------------------------------------------------
-- | Weaken a 'Union' so it is capable of storing a number of new effects
-- somewhere within the previous effect list.
-- Both the prefix and the new effects are specified as singleton list proofs.
weakenMid :: forall right m a left mid
           . SList left -> SList mid
          -> Union (Append left right) m a
          -> Union (Append left (Append mid right)) m a
weakenMid sl sm (Union pr e) = Union (injectMembership @right sl sm pr) e
{-# INLINABLE weakenMid #-}

------------------------------------------------------------------------------
-- | Attempt to take an @e@ effect out of a 'Union'.
prj :: forall e r m a
     . ( Member e r
       )
    => Union r m a
    -> Maybe (Weaving e m a)
prj = prjUsing membership
{-# INLINABLE prj #-}

------------------------------------------------------------------------------
-- | Attempt to take an @e@ effect out of a 'Union', given an explicit
-- proof that the effect exists in @r@.
prjUsing
  :: forall e r m a
   . ElemOf e r
  -> Union r m a
  -> Maybe (Weaving e m a)
prjUsing pr (Union sn a) = (\Refl -> a) <$> sameMember pr sn
{-# INLINABLE prjUsing #-}

------------------------------------------------------------------------------
-- | Like 'decomp', but allows for a more efficient
-- 'Polysemy.rewrite' function.
decompCoerce
    :: Union (e ': r) m a
    -> Either (Union (f ': r) m a) (Weaving e m a)
decompCoerce (Union p a) =
  case p of
    Here  -> Right a
    There pr -> Left (Union (There pr) a)
{-# INLINABLE decompCoerce #-}
