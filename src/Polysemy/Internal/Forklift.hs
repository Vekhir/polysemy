{-# LANGUAGE NumDecimals     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

{-# OPTIONS_HADDOCK not-home #-}

module Polysemy.Internal.Forklift where

import qualified Control.Concurrent.Async as A
import           Control.Concurrent.Chan.Unagi
import           Control.Concurrent.MVar
import           Control.Monad
import           Polysemy.Internal
import           Polysemy.Internal.Union


------------------------------------------------------------------------------
-- | A promise for interpreting an effect of the union @r@ in another thread.
--
-- @since 0.5.0.0
data Forklift r = forall a. Forklift
  { responseMVar :: MVar (Sem '[Embed IO] a)
  , request      :: Union r (Sem r) a
  }


------------------------------------------------------------------------------
-- | A strategy for automatically interpreting an entire stack of effects by
-- just shipping them off to some other interpretation context.
--
-- @since 0.5.0.0
runViaForklift
    :: LastMember (Embed IO) r
    => InChan (Forklift r)
    -> Sem r a
    -> Sem '[Embed IO] a
runViaForklift chan (Sem m) = Sem $ \k -> m $ \u -> do
  case decompLast u of
    Left x -> usingSem k $ join $ embed $ do
      mvar <- newEmptyMVar
      writeChan chan $ Forklift mvar x
      takeMVar mvar
    Right y -> k $ hoist (runViaForklift chan) y
{-# INLINE runViaForklift #-}



------------------------------------------------------------------------------
-- | Run an effect stack all the way down to 'IO' by running it in a new
-- thread, and temporarily turning the current thread into an event poll.
--
-- This function creates a thread, and so should be compiled with @-threaded@.
--
-- @since 0.5.0.0
withLowerToIO
    :: LastMember (Embed IO) r
    => ((forall x. Sem r x -> IO x) -> IO () -> IO a)
       -- ^ A lambda that takes the lowering function, and a finalizing 'IO'
       -- action to mark a the forked thread as being complete. The finalizing
       -- action need not be called.
    -> Sem r a
withLowerToIO action = do
  (inchan, outchan) <- embed newChan
  signal <- embed newEmptyMVar

  res <- embed $ A.async $ do
    a <- action (runM . runViaForklift inchan)
                (putMVar signal ())
    putMVar signal ()
    pure a

  let me = do
        raced <- embed $ A.race (takeMVar signal) $ readChan outchan
        case raced of
          Left () -> embed $ A.wait res
          Right (Forklift mvar req) -> do
            resp <- liftSem req
            embed $ putMVar mvar $ pure resp
            me_b
      {-# INLINE me #-}

      me_b = me
      {-# NOINLINE me_b #-}

  me
