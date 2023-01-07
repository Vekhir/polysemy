{-# LANGUAGE TupleSections #-}

-- | Description: Interpreters for 'Writer'
module Polysemy.Writer
  ( -- * Effect
    Writer (..)

    -- * Actions
  , tell
  , listen
  , pass
  , censor

    -- * Interpretations
  , runWriter
  , runLazyWriter
  , runWriterAssocR
  , runLazyWriterAssocR
  , runWriterTVar
  , writerToIOFinal
  , writerToIOAssocRFinal
  , writerIntoEndoWriter

    -- * Interpretations for Other Effects
  , outputToWriter
  ) where

import Control.Concurrent.STM
import qualified Control.Monad.Trans.Writer.Lazy as Lazy

import Data.Bifunctor (first)
import Data.Semigroup

import Polysemy
import Polysemy.Output
import Polysemy.State
import Polysemy.HigherOrder

import Polysemy.Internal.Union
import Polysemy.Internal.Writer



------------------------------------------------------------------------------
-- | @since 0.7.0.0
censor :: Member (Writer o) r
       => (o -> o)
       -> Sem r a
       -> Sem r a
censor f m = pass $ (f ,) <$> m

------------------------------------------------------------------------------
-- | Transform an 'Output' effect into a 'Writer' effect.
--
-- @since 1.0.0.0
outputToWriter :: Member (Writer o) r => Sem (Output o ': r) a -> Sem r a
outputToWriter = interpret $ \case
  Output o -> tell o


------------------------------------------------------------------------------
-- | Run a 'Writer' effect in the style of
-- 'Control.Monad.Trans.Writer.Strict.WriterT'
-- (but without the nasty space leak!)
runWriter
    :: Monoid o
    => Sem (Writer o ': r) a
    -> Sem r (o, a)
runWriter = runState mempty . reinterpretH
  (\case
      Tell o -> modify' (<> o)
      Listen m -> do
        -- runExposeH' to prevent local failures from ruining our day
        (o, ta) <- runWriter (runExposeH' m)
        modify' (<> o)
        a <- restoreH ta
        return (o, a)
      Pass m -> do
        (o, t) <- runWriter (runExposeH' m)
        -- Try to extract the modification function from the t.
        -- If "m" failed, default to id.
        let f = foldr (const . fst) id t
        modify' (<> f o)
        (_, a) <- restoreH t
        return a
  )


------------------------------------------------------------------------------
-- | Run a 'Writer' effect in the style of 'Control.Monad.Trans.Writer.WriterT'
-- lazily.
--
-- __Warning: This inherits the nasty space leak issue of__
-- __'Lazy.WriterT'! Don't use this if you don't have to.__
--
-- @since 1.3.0.0
runLazyWriter
    :: forall o r a
     . Monoid o
    => Sem (Writer o ': r) a
    -> Sem r (o, a)
runLazyWriter = interpretViaLazyWriter $ \(Weaving e mkT lwr ex) ->
  case e of
    Tell o   -> ex (mkInitState lwr) <$ Lazy.tell o
    Listen m -> do
      let m' = lwr $ mkT id m
      ~(fa, o) <- Lazy.listen m'
      return $ ex $ (,) o <$> fa
    Pass m -> do
      let m' = lwr $ mkT id m
      Lazy.pass $ do
        ft <- m'
        let f = foldr (const . fst) id ft
        return (ex $ snd <$> ft, f)

-----------------------------------------------------------------------------
-- | Like 'runWriter', but right-associates uses of '<>'.
--
-- This asymptotically improves performance if the time complexity of '<>'
-- for the 'Monoid' depends only on the size of the first argument.
--
-- You should always use this instead of 'runWriter' if the monoid
-- is a list, such as 'String'.
--
-- @since 1.1.0.0
runWriterAssocR
    :: Monoid o
    => Sem (Writer o ': r) a
    -> Sem r (o, a)
runWriterAssocR =
    (fmap . first) (`appEndo` mempty)
  . runWriter
  . writerIntoEndoWriter


-----------------------------------------------------------------------------
-- | Like 'runLazyWriter', but right-associates uses of '<>'.
--
-- This asymptotically improves performance if the time complexity of '<>'
-- for the 'Monoid' depends only on the size of the first argument.
--
-- You should always use this instead of 'runLazyWriter' if the monoid
-- is a list, such as 'String'.
--
-- __Warning: This inherits the nasty space leak issue of__
-- __'Lazy.WriterT'! Don't use this if you don't have to.__
--
-- @since 1.3.0.0
runLazyWriterAssocR
    :: Monoid o
    => Sem (Writer o ': r) a
    -> Sem r (o, a)
runLazyWriterAssocR =
    (fmap . first) (`appEndo` mempty)
  . runLazyWriter
  . writerIntoEndoWriter

--------------------------------------------------------------------
-- | Transform a 'Writer' effect into atomic operations
-- over a 'TVar' through final 'IO'.
--
-- @since 1.2.0.0
runWriterTVar :: (Monoid o, Member (Final IO) r)
              => TVar o
              -> Sem (Writer o ': r) a
              -> Sem r a
runWriterTVar tvar = runWriterSTMAction $ \o -> do
  s <- readTVar tvar
  writeTVar tvar $! s <> o


--------------------------------------------------------------------
-- | Run a 'Writer' effect by transforming it into atomic operations
-- through final 'IO'.
--
-- Internally, this simply creates a new 'TVar', passes it to
-- 'runWriterTVar', and then returns the result and the final value
-- of the 'TVar'.
--
-- /Note/: Effects that aren't interpreted in terms of 'IO'
-- will have local state semantics in regards to 'Writer' effects
-- interpreted this way. See 'Final'.
--
-- @since 1.2.0.0
writerToIOFinal :: (Monoid o, Member (Final IO) r)
                => Sem (Writer o ': r) a
                -> Sem r (o, a)
writerToIOFinal sem = do
  tvar <- embedFinal $ newTVarIO mempty
  res  <- runWriterTVar tvar sem
  end  <- embedFinal $ readTVarIO tvar
  return (end, res)

--------------------------------------------------------------------
-- | Like 'writerToIOFinal'. but right-associates uses of '<>'.
--
-- This asymptotically improves performance if the time complexity of '<>'
-- for the 'Monoid' depends only on the size of the first argument.
--
-- You should always use this instead of 'writerToIOFinal' if the monoid
-- is a list, such as 'String'.
--
-- /Note/: Effects that aren't interpreted in terms of 'IO'
-- will have local state semantics in regards to 'Writer' effects
-- interpreted this way. See 'Final'.
--
-- @since 1.2.0.0
writerToIOAssocRFinal :: (Monoid o, Member (Final IO) r)
                      => Sem (Writer o ': r) a
                      -> Sem r (o, a)
writerToIOAssocRFinal =
    (fmap . first) (`appEndo` mempty)
  . writerToIOFinal
  . writerIntoEndoWriter
