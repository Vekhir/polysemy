{-# LANGUAGE GeneralizedNewtypeDeriving, QuantifiedConstraints, TupleSections #-}
{-# OPTIONS_HADDOCK not-home #-}
module Polysemy.Internal.WeaveClass
  ( MonadTransWeave(..)
  , mkInitState
  , ComposeT(..)
  , LazyT2(..)
  ) where

import Control.Monad
import Control.Monad.Trans
import qualified Control.Monad.Trans.Except as E
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.State.Lazy as LSt
import qualified Control.Monad.Trans.State.Strict as SSt
import qualified Control.Monad.Trans.Writer.Lazy as LWr
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Tuple
import Data.Foldable
import Polysemy.Internal.Utils
import Data.Kind (Type)

-- | A variant of the classic @MonadTransControl@ class from @monad-control@,
-- but with a small number of changes to make it more suitable for Polysemy's
-- internals.
class ( MonadTrans t
      , forall z. Monad z => Monad (t z)
      , Traversable (StT t)
      )
   => MonadTransWeave t where
  type StT t :: Type -> Type

  hoistT :: (Monad m, Monad n)
         => (forall x. m x -> n x)
         -> t m a -> t n a
  hoistT n m = controlT $ \lower -> n (lower m)
  {-# INLINE hoistT #-}

  controlT :: Monad m
           => ((forall z x. Monad z => t z x -> z (StT t x)) -> m (StT t a))
           -> t m a
  controlT main = liftWith main >>= restoreT . pure
  {-# INLINE controlT #-}

  liftWith :: Monad m
           => ((forall z x. Monad z => t z x -> z (StT t x)) -> m a)
           -> t m a

  restoreT :: Monad m => m (StT t a) -> t m a

newtype ComposeT t (u :: (Type -> Type) -> Type -> Type) m a = ComposeT {
    getComposeT :: t (u m) a
  }
  deriving (Functor, Applicative, Monad)

instance ( MonadTrans t
         , MonadTrans u
         , forall m. Monad m => Monad (u m)
         )
      => MonadTrans (ComposeT t u) where
  lift m = ComposeT (lift (lift m))

instance ( MonadTransWeave t
         , MonadTransWeave u
         )
      => MonadTransWeave (ComposeT t u) where
  type StT (ComposeT t u) = Compose (StT u) (StT t)

  hoistT n (ComposeT m) = ComposeT (hoistT (hoistT n) m)

  controlT main = ComposeT $
    controlT $ \lowerT ->
    controlT $ \lowerU ->
    getCompose <$> main (\(ComposeT m) -> Compose <$> lowerU (lowerT m))

  liftWith main = ComposeT $
    liftWith $ \lowerT ->
    liftWith $ \lowerU ->
    main (\(ComposeT m) -> Compose <$> lowerU (lowerT m))

  restoreT m = ComposeT (restoreT (restoreT (fmap getCompose m)))

mkInitState :: Monad (t Identity)
            => (t Identity () -> Identity (StT t ()))
            -> StT t ()
mkInitState lwr = runIdentity $ lwr (pure ())
{-# INLINE mkInitState #-}

instance MonadTransWeave IdentityT where
  type StT IdentityT = Identity
  hoistT nt = IdentityT . nt . runIdentityT

  liftWith main = IdentityT (main (fmap Identity . runIdentityT))

  controlT main = IdentityT (runIdentity <$> main (fmap Identity . runIdentityT))

  restoreT = IdentityT . fmap runIdentity

instance MonadTransWeave (LSt.StateT s) where
  type StT (LSt.StateT s) = LazyT2 s

  hoistT nt = LSt.mapStateT nt

  controlT main = LSt.StateT $ \s ->
    (\(LazyT2 ~(s', a)) -> (a, s'))
    <$> main (\m -> (\ ~(a, s') -> LazyT2 (s', a)) <$> LSt.runStateT m s)

  liftWith main = LSt.StateT $ \s ->
        (, s)
    <$> main (\m -> (\ ~(a, s') -> LazyT2 (s', a)) <$> LSt.runStateT m s)

  restoreT m = LSt.StateT $ \_ -> (\(LazyT2 ~(s, a)) -> (a, s)) <$> m

instance MonadTransWeave (SSt.StateT s) where
  type StT (SSt.StateT s) = (,) s

  hoistT nt = SSt.mapStateT nt

  controlT main = SSt.StateT $ \s ->
    swap <$!> main (\m -> swap <$!> SSt.runStateT m s)

  liftWith main = SSt.StateT $ \s ->
        (, s)
    <$> main (\m -> swap <$!> SSt.runStateT m s)

  restoreT m = SSt.StateT $ \_ -> swap <$!> m

instance MonadTransWeave (E.ExceptT e) where
  type StT (E.ExceptT e) = Either e

  hoistT nt = E.mapExceptT nt

  controlT main = E.ExceptT (main E.runExceptT)

  liftWith main = lift $ main E.runExceptT

  restoreT = E.ExceptT

instance Monoid w => MonadTransWeave (LWr.WriterT w) where
  type StT (LWr.WriterT w) = LazyT2 w

  hoistT nt = LWr.mapWriterT nt

  controlT main = LWr.WriterT $
    (\(LazyT2 ~(s, a)) -> (a, s))
    <$> main (fmap (\ ~(a, s) -> LazyT2 (s, a)) . LWr.runWriterT)

  liftWith main = lift $ main (fmap (\ ~(a, s) -> LazyT2 (s, a)) . LWr.runWriterT)

  restoreT m = LWr.WriterT ((\(LazyT2 ~(s, a)) -> (a, s)) <$> m)


instance MonadTransWeave MaybeT where
  type StT MaybeT = Maybe

  hoistT nt = mapMaybeT nt

  controlT main = MaybeT (main runMaybeT)

  liftWith main = lift $ main runMaybeT

  restoreT = MaybeT

newtype LazyT2 s a = LazyT2 { getLazyT2 :: (s, a) }

instance Functor (LazyT2 s) where
  fmap f (LazyT2 ~(s, a)) = LazyT2 (s, f a)
  a <$ (LazyT2 ~(s, _)) = LazyT2 (s, a)

instance Foldable (LazyT2 s) where
  length _ = 1
  foldr c b (LazyT2 ~(_, a)) = c a b
  foldMap f (LazyT2 ~(_, a)) = f a
  toList (LazyT2 ~(_, a)) = [a]

instance Traversable (LazyT2 s) where
  traverse f (LazyT2 ~(s, a)) = (LazyT2 #. (,) s) <$> f a
