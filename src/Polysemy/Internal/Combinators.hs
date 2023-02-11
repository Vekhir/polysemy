{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns   #-}
{-# OPTIONS_HADDOCK not-home #-}

-- | Description: The basic interpreter-building combinators
module Polysemy.Internal.Combinators
  ( -- * First order
    rewrite
  , rewriteAt
  , transform
  , transformUsing

    -- * Statefulness
  , stateful
  , lazilyStateful
  ) where

import Data.Coerce
import Data.Type.Equality
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Sing
import Polysemy.Internal.Core
import Polysemy.Internal.Membership
import Polysemy.Internal.Utils
import Polysemy.Internal.WeaveClass

runWeaveState :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
runWeaveState s0' sem0' = go s0' sem0'
  where
    go :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
    go s0 sem0 = Sem $ \k c0 ->
      let
        g' = mapHandlers
          (\f wav c s ->
            f (weave (s, ()) (uncurry runWeaveState) (runWeaveState s) wav)
              (\(s', x) -> c x s')
          ) k
        -- {-# INLINE g' #-}

        AHandler h = AHandler $ \wav c s -> fromFOEff wav $ \ex -> \case
          RestoreW (s', a) -> c (ex a) s'
          GetStateW main -> c (ex (main ((,) s))) s
          LiftWithW main -> c (ex (main (go_ s))) s
          EmbedW m -> runSem m k (\a -> c (ex a) s)

        !k' = mkHandlers $ consHandler' h g'
      in
        runSem sem0
          k'
          (\a s -> c0 (s, a))
          s0
    -- {-# INLINE go #-}

    go_ :: s -> Sem (Weave ((,) s) r ': r) a -> Sem r (s, a)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE runWeaveState #-}

runWeaveLazyState :: s -> Sem (Weave (LazyT2 s) r ': r) a -> Sem r (LazyT2 s a)
runWeaveLazyState s0 sem0 = Sem $ \k c0 ->
  let
    g' = mapHandlers
      (\f wav c s ->
        f (weave
            (LazyT2 (s, ()))
            (\(LazyT2 ~(s', sem)) -> coerce $ runWeaveLazyState s' sem)
            (coerce #. runWeaveLazyState s)
            wav
          )
          (\(LazyT2 ~(s', x)) -> c x s')
      ) k

    AHandler h = AHandler $ \wav c s -> fromFOEff wav $ \ex -> \case
      RestoreW (LazyT2 ~(s', a)) -> c (ex a) s'
      GetStateW main -> c (ex (main (LazyT2 #. (,) s))) s
      LiftWithW main -> c (ex (main (runWeaveLazyState s))) s
      EmbedW m -> runSem m k (\a -> c (ex a) s)
  in
    runSem sem0
      (mkHandlers $ consHandler' h g')
      (\a s -> c0 $ LazyT2 (s, a))
      s0

------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
stateful
    :: forall s e r a
     . (∀ x m. e m x -> s -> Sem r (s, x))
    -> s -> Sem (e ': r) a -> Sem r (s, a)
stateful f = go
  where
    go :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go s0 sem0 = Sem $ \k c0 ->
      let
        g' = mapHandlers
          (\f wav c s ->
            f (weave (s, ()) (uncurry go_) (runWeaveState s) wav)
              (\(s', x) -> c x s')
          ) k
        -- {-# INLINE g' #-}

        AHandler h = AHandler $ \wav c s -> fromFOEff wav $ \ex e ->
          runSem (f e s) k (\(s', x) -> c (ex x) s')

        !k' = mkHandlers $ consHandler' h g'
      in
        runSem sem0 k' (\a s -> c0 (s, a)) s0
    -- {-# INLINE go #-}

    go_ :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE[3] stateful #-}


------------------------------------------------------------------------------
-- | Like 'interpret', but with access to an intermediate state @s@.
lazilyStateful
    :: forall e s r a
     . (∀ x m. e m x -> s -> Sem r (s, x))
    -> s
    -> Sem (e ': r) a
    -> Sem r (s, a)
lazilyStateful f = go
  where
    go :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go s0 sem0 = Sem $ \k c0 ->
      let
        AHandler !h = AHandler $ \wav c s -> fromFOEff wav $ \ex e ->
          runSem (f e s) k (\ ~(s', x) -> c (ex x) s')

        !handlers = mkHandlers $ consHandler' h $ mapHandlers
          (\f wav c s ->
            f (weave
                (LazyT2 (s, ()))
                (\(LazyT2 ~(s', sem)) -> coerce $ go_ s' sem)
                (coerce #. runWeaveLazyState s)
                wav
              )
              (\(LazyT2 ~(s', x)) -> c x s')
          ) k
      in
        runSem sem0
          handlers
          (\a s -> c0 (s, a))
          s0
    -- {-# INLINE go #-}

    go_ :: forall x. s -> Sem (e ': r) x -> Sem r (s, x)
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINE[3] lazilyStateful #-}

------------------------------------------------------------------------------
-- | Rewrite an effect @e1@ directly into @e2@, and put it on the top of the
-- effect stack.
--
-- @'rewrite' n = 'interpretH' ('propagate' . n)@
--
-- @since 1.2.3.0
rewrite
    :: forall e2 e1 r a
     . (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem (e2 ': r) a
rewrite f = reinterpretViaHandlerFast $ \_ hs ->
  let
    AHandler !h = AHandler $ getHandler' hs Here
  in
    \w -> h (rewriteWeaving f w)
{-# INLINEABLE rewrite #-}

rewriteAt
    :: forall l e2 e1 r a
     . SList l
    -> (forall z x. e1 z x -> e2 z x)
    -> Sem (Append l (e1 ': r)) a
    -> Sem (Append l (e2 ': r)) a
rewriteAt sl f = go
  where
    rewriteAtHS :: HandlerTrans (Append l (e1 ': r)) (Append l (e2 ': r))
    rewriteAtHS (Handlers n hs) =
      let
        AHandler !e2h = AHandler $ getHandler' hs (memberAt @r sl)
        AHandler e1h = AHandler $ \w -> e2h (rewriteWeaving f w)
      in
        Handlers (n . go_) $ replaceHandler' @r @e2 sl e1h hs

    go :: forall x. Sem (Append l (e1 ': r)) x -> Sem (Append l (e2 ': r)) x
    go = hoistSem rewriteAtHS
    -- {-# INLINE go #-}

    go_ :: forall x. Sem (Append l (e1 ': r)) x -> Sem (Append l (e2 ': r)) x
    go_ = go
    {-# NOINLINE go_ #-}
{-# INLINEABLE rewriteAt #-}


------------------------------------------------------------------------------
-- | Transform an effect @e1@ into an effect @e2@ that is already somewhere
-- inside of the stack.
--
-- @since 1.2.3.0
transform
    :: forall e2 e1 r a
     . Member e2 r
    => (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem r a
transform = transformUsing membership
-- -- {-# INLINE transform #-}

transformUsing
    :: forall e2 e1 r a
     . ElemOf e2 r
    -> (forall z x. e1 z x -> e2 z x)
    -> Sem (e1 ': r) a
    -> Sem r a
transformUsing pr f = interpretViaHandlerFast $ \_ hs ->
  let
    AHandler !h = AHandler (getHandler' hs pr)
  in
    \w -> h (rewriteWeaving f w)
{-# INLINEABLE transformUsing #-}
