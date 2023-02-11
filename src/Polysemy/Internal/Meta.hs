{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}

module Polysemy.Internal.Meta where

import Control.Monad

import Data.Functor.Identity
import Data.Kind (Type)
import Data.Unique
import Data.Type.Equality

import Polysemy
import Polysemy.Bundle
import Polysemy.Membership
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Internal.Utils
import Polysemy.Internal.HigherOrder
import Polysemy.Internal.Reflection
import Polysemy.Internal.Core
import Polysemy.Internal.Combinators
import System.IO.Unsafe
import Unsafe.Coerce
import GHC.Exts (inline)

type MetaEffect = [(Type -> Type, Effect)] -> Effect

data MetaRun :: Effect where
  MetaRun :: forall eff m a. Unique -> eff m a -> MetaRun m a

type (:%) a b = '(a, b)

data Meta (metaeff :: MetaEffect) :: Effect where
  MetaMetaRun :: forall metaeff m a
               . Unique -> MetaRun m a -> Meta metaeff m a
  SendMeta :: forall metaeff l z m a
            . metaeff l z a
           -> (forall x. z x -> m x)
           -> (forall eff q x. Unique -> Unique -> ElemOf '(q, eff) l -> q x -> m x)
           -> Meta metaeff m a

splitMeta :: Unique
          -> Sem (Meta metaeff ': r) a
          -> Sem (Meta metaeff ': MetaRun ': r) a
splitMeta uniq = go
  where
    splitMetaHS :: HandlerTrans (Meta metaeff ': r) (Meta metaeff ': MetaRun ': r)
    splitMetaHS (Handlers n hs) =
      let
        AHandler hM = AHandler $ \wav ->
          case wav & rewriteWeaving' \case
            MetaMetaRun uniq' metarun
              | uniq == uniq' -> Bundle (There Here) metarun
            other -> Bundle Here other
          of
            Union pr wav' -> getHandler' hs pr wav'
      in
        Handlers (n . go_) (hM `consHandler'` dropHandlers' @'[_, _] hs)

    go :: Sem (Meta metaeff ': r) a -> Sem (Meta metaeff ': MetaRun ': r) a
    go = hoistSem splitMetaHS
    -- {-# INLINE go #-}

    go_ :: Sem (Meta metaeff ': r) a -> Sem (Meta metaeff ': MetaRun ': r) a
    go_ = go
    {-# NOINLINE go_ #-}
-- {-# INLINE splitMeta #-}

class AllSemRaises l r
instance AllSemRaises '[] r
instance (t ~ '(Sem (eff ': r), eff), AllSemRaises l' r)
      => AllSemRaises (t ': l') r

proveSemRaise :: forall l r eff z
               . AllSemRaises l r => ElemOf '(z, eff) l -> z :~: Sem (eff ': r)
proveSemRaise !_ = unsafeCoerce Refl
-- {-# INLINE proveSemRaise #-}

sendMeta :: forall metaeff l r a
          . (Member (Meta metaeff) r, AllSemRaises l r)
         => metaeff l (Sem r) a
         -> Sem r a
sendMeta = sendMetaUsing membership
-- {-# INLINE sendMeta #-}

sendMetaUsing :: forall metaeff l r a
               . AllSemRaises l r
              => ElemOf (Meta metaeff) r
              -> metaeff l (Sem r) a
              -> Sem r a
sendMetaUsing pr = sendMetaViaUsing pr
                    id
                    (\pr' -> case proveSemRaise @l @r pr' of Refl -> id)
-- {-# INLINE sendMetaUsing #-}

sendMetaVia :: forall metaeff l m r a
             . Member (Meta metaeff) r
            => (forall x. m x -> Sem r x)
            -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
            -> metaeff l m a
            -> Sem r a
sendMetaVia = sendMetaViaUsing membership
-- {-# INLINE sendMetaVia #-}

sendMetaViaUsing
  :: forall metaeff l m r a
   . ElemOf (Meta metaeff) r
  -> (forall x. m x -> Sem r x)
  -> (forall eff z x. ElemOf '(z, eff) l -> z x -> Sem (eff ': r) x)
  -> metaeff l m a
  -> Sem r a
sendMetaViaUsing pr to1 to2 p = sendUsing pr $ SendMeta p to1 $
  \uniq effUniq pr' ->
    transformUsing pr (MetaMetaRun @metaeff uniq . MetaRun effUniq)
    . to2 pr'
{-# INLINE sendMetaViaUsing #-}

metaToMeta ::
  ∀ metaeff1 metaeff0 r.
  Member (Meta metaeff1) r =>
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMeta = metaToMetaUsing membership
-- {-# INLINE metaToMeta #-}

metaToMetaUsing ::
  ∀ metaeff1 metaeff0 r.
  ElemOf (Meta metaeff1) r ->
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  InterpreterFor (Meta metaeff0) r
metaToMetaUsing pr n = transformUsing pr \case
  MetaMetaRun uniq metarun -> MetaMetaRun uniq metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2
{-# INLINEABLE metaToMetaUsing #-}

metaIntoMeta ::
  ∀ metaeff1 metaeff0 r.
  (forall l m x. metaeff0 l m x -> metaeff1 l m x) ->
  (forall x. Sem (Meta metaeff0 ': r) x -> Sem (Meta metaeff1 ': r) x)
metaIntoMeta n = rewrite \case
  MetaMetaRun uniq metarun -> MetaMetaRun uniq metarun
  SendMeta metaeff to1 to2 -> SendMeta (n metaeff) to1 to2
{-# INLINEABLE metaIntoMeta #-}

mkIntoMeta :: ∀ metaeff m x. metaeff '[] m x -> Meta metaeff m x
mkIntoMeta e = SendMeta e id (\_ _ u _ -> absurdMembership u)
-- {-# INLINE mkIntoMeta #-}

type family ProcessorWithMeta metaeff (b :: Bool) (tail :: EffectRow) where
  ProcessorWithMeta metaeff 'True tail = Meta metaeff ': tail
  ProcessorWithMeta metaeff b tail = tail

newtype ProcessorMetaUsing (b :: Bool) metaeff t rH l = ProcessorMetaUsing {
    unProcessorMetaUsing
      :: forall q eff x y
       . ElemOf '(q, eff) l
      -> t x
      -> (x -> q y)
      -> Sem (eff
              ': ProcessorWithMeta metaeff b
                 (HandlingMeta metaeff t rH l ': rH)) (t y)
  }

newtype ProcessorMeta (b :: Bool) metaeff t rH l = ProcessorMeta {
    unProcessorMeta
      :: forall q eff x y
       . DepMember eff q l
      => t x
      -> (x -> q y)
      -> Sem (eff
              ': ProcessorWithMeta metaeff b
                 (HandlingMeta metaeff t rH l ': rH)) (t y)
  }

data HandlingMeta metaeffect t rH l :: Effect where
  HandlingMetaMetaRun
    :: forall metaeffect t rH l m a
     . MetaRun m a -> HandlingMeta metaeffect t rH l m a
  ProcessMeta
    :: forall eff q metaeffect t rH l m x y
     . ElemOf '(q, eff) l
    -> t x
    -> (x -> q y)
    -> HandlingMeta metaeffect t rH l m
        (Sem (eff ': HandlingMeta metaeffect t rH l ': rH) (t y))
  ProcessMeta'
    :: forall eff q metaeffect t rH l m x y
     . ElemOf '(q, eff) l
    -> t x
    -> (x -> q y)
    -> HandlingMeta metaeffect t rH l m
        (Sem (eff ': Meta metaeffect
              ': HandlingMeta metaeffect t rH l ': rH) (t y))

data Box where
  Box :: a -> Box

newUniqueIO :: Box -> IO Unique
newUniqueIO (Box _) = newUnique
{-# NOINLINE newUniqueIO #-}

newUniqueSem :: Sem r Unique
newUniqueSem = Sem $ \_ c ->
  let
    uniq = unsafePerformIO (newUniqueIO (Box c))
    {-# NOINLINE uniq #-}
  in
    uniq `seq` c uniq
{-# NOINLINE newUniqueSem #-}

class DepMember eff z l | z l -> eff where
  depMembership :: ElemOf '(z, eff) l

instance {-# OVERLAPPING #-}
      eff ~ eff'
  => DepMember eff z ('(z, eff') ': l) where
  depMembership = Here
  -- {-# INLINE depMembership #-}

instance DepMember eff z l
      => DepMember eff z (_t : l) where
  depMembership = There depMembership

getProcessorMetaUsing
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMetaUsing 'False metaeff t rH l)
getProcessorMetaUsing = return (ProcessorMetaUsing metaProcessorUsing)
-- {-# INLINE getProcessorMetaUsing #-}

getProcessorMetaUsing'
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMetaUsing 'True metaeff t rH l)
getProcessorMetaUsing' = return (ProcessorMetaUsing metaProcessorUsing')
-- {-# INLINE getProcessorMetaUsing' #-}

getProcessorMeta
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMeta 'False metaeff t rH l)
getProcessorMeta = return (ProcessorMeta (metaProcessorUsing depMembership))
-- {-# INLINE getProcessorMeta #-}

getProcessorMeta'
  :: forall r metaeff z t rH rC l mh
   . mh ~ HandlingMeta metaeff t rH l
  => Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
         (ProcessorMeta 'True metaeff t rH l)
getProcessorMeta' = return (ProcessorMeta (metaProcessorUsing' depMembership))
-- {-# INLINE getProcessorMeta' #-}

metaProcessorUsing
  :: forall q eff metaeff t r l x y
   . ElemOf '(q, eff) l
  -> t x
  -> (x -> q y)
  -> Sem (eff ': HandlingMeta metaeff t r l ': r) (t y)
metaProcessorUsing =
  \pr t ex -> join $ sendUsing (There Here) (ProcessMeta pr t ex)
-- {-# INLINE metaProcessorUsing #-}

metaProcessorUsing'
  :: forall q eff metaeff t r l x y
   . ElemOf '(q, eff) l
  -> t x
  -> (x -> q y)
  -> Sem (eff ': Meta metaeff ': HandlingMeta metaeff t r l ': r) (t y)
metaProcessorUsing' =
  \pr t ex -> join $ sendUsing (There (There Here)) (ProcessMeta' pr t ex)
-- {-# INLINE metaProcessorUsing' #-}

processMetaUsing :: forall r eff q metaeff z t rH rC l a mh
                  . mh ~ HandlingMeta metaeff t rH l
                 => ElemOf '(q, eff) l
                 -> q a
                 -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                        (Sem (eff ': mh ': rH) (t a))
processMetaUsing pr q = do
  fmap (\t -> metaProcessorUsing pr t (\_ -> q)) getStateH
-- {-# INLINE processMetaUsing #-}

processMetaUsing' :: forall r eff q metaeff z t rH rC l a mh
                   . mh ~ HandlingMeta metaeff t rH l
                  => ElemOf '(q, eff) l
                  -> q a
                  -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r)
                         (Sem (eff ': Meta metaeff ': mh ': rH) (t a))
processMetaUsing' pr q = do
  fmap (\t -> metaProcessorUsing' pr t (\_ -> q)) getStateH
-- {-# INLINE processMetaUsing' #-}

runMeta :: forall r eff q metaeff z t rH rC l a b mh
         . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
        => (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
        -> q a
        -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta = runMetaUsing depMembership
-- {-# INLINE runMeta #-}

runMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
              . mh ~ HandlingMeta metaeff t rH l
             => ElemOf '(q, eff) l
             -> (Sem (eff ': mh ': rH) (t a) -> Sem rC (t b))
             -> q a
             -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing pr interp = runExposeMetaUsing pr interp >=> restoreH
-- {-# INLINE runMetaUsing #-}

runMeta' :: forall r eff q metaeff z t rH rC l a b mh
          . (DepMember eff q l , mh ~ HandlingMeta metaeff t rH l)
         => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
         -> q a
         -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMeta' = runMetaUsing' depMembership
-- {-# INLINE runMeta' #-}

runMetaUsing' :: forall r eff q metaeff z t rH rC l a b mh
               . mh ~ HandlingMeta metaeff t rH l
              => ElemOf '(q, eff) l
              -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC (t b))
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runMetaUsing' pr interp = runExposeMetaUsing' pr interp >=> restoreH
-- {-# INLINE runMetaUsing' #-}

runExposeMeta :: forall r eff q metaeff z t rH rC l a b mh
               . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
              => (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
              -> q a
              -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta = runExposeMetaUsing depMembership
-- {-# INLINE runExposeMeta #-}

runExposeMeta' :: forall r eff q metaeff z t rH rC l a b mh
                . (DepMember eff q l, mh ~ HandlingMeta metaeff t rH l)
               => (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
               -> q a
               -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMeta' = runExposeMetaUsing' depMembership
-- {-# INLINE runExposeMeta' #-}

runExposeMetaUsing :: forall r eff q metaeff z t rH rC l a b mh
                    . mh ~ HandlingMeta metaeff t rH l
                   => ElemOf '(q, eff) l
                   -> (Sem (eff ': mh ': rH) (t a) -> Sem rC b)
                   -> q a
                   -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing pr interp = processMetaUsing pr >=> embedH . interp
-- {-# INLINE runExposeMetaUsing #-}

runExposeMetaUsing' :: forall r metaeff eff q z t rH rC l a b mh
                     . mh ~ HandlingMeta metaeff t rH l
                    => ElemOf '(q, eff) l
                    -> (Sem (eff ': Meta metaeff ': mh ': rH) (t a) -> Sem rC b)
                    -> q a
                    -> Sem (HigherOrder z t (Meta metaeff) (mh ': rH) rC ': r) b
runExposeMetaUsing' pr interp = processMetaUsing' pr >=> embedH . interp
-- {-# INLINE runExposeMetaUsing' #-}

type MetaHandler metaeff r =
   (   forall l t z x mh
     . (Traversable t, mh ~ HandlingMeta metaeff t r l)
    => metaeff l z x
    -> Sem (HigherOrder z t (Meta metaeff) (mh ': r) (mh ': r) ': mh ': r) x
   )

exposeMetaRun :: forall eff r a
               . ElemOf MetaRun r
              -> Unique -> Sem r a -> Sem (eff ': r) a
exposeMetaRun pr uniq = go
  where
    exposeMetaRunHS :: HandlerTrans r (eff ': r)
    exposeMetaRunHS (Handlers n hs) =
      let
        AHandler h = AHandler $ \wav ->
          case wav & rewriteWeaving' \case
            MetaRun uniq' act
              | uniq == uniq' -> Bundle Here (unsafeCoerce act)
            metarun -> Bundle (There pr) metarun
          of
            Union pr wav' -> getHandler' hs pr wav'
      in
        Handlers (n . go_) (interceptHandler' pr h (dropHandlers' @'[_] hs))
    go :: forall x. Sem r x -> Sem (eff ': r) x
    go = hoistSem exposeMetaRunHS
    -- {-# INLINE go #-}

    go_ :: forall x. Sem r x -> Sem (eff ': r) x
    go_ = go
    {-# NOINLINE go_ #-}
-- {-# INLINE exposeMetaRun #-}

interpretMeta
  :: forall metaeff r
   . MetaHandler metaeff r
  -> InterpreterFor (Meta metaeff) r
interpretMeta h = \m -> do
  uniq <- newUniqueSem
  let
      bomb :: Unique -> Unique -> a
      bomb uniq' effUniq' = errorWithoutStackTrace
        ("Stray MetaMetaRun! Report this as a bug on the polysemy GitHub repo."
         ++ "\tWith interpretMeta unique " ++ show (hashUnique uniq')
         ++ ", and with MetaRun unique " ++ show (hashUnique effUniq') ++ "\n"
         ++ "\tCurrent interpretMeta unique is " ++ show (hashUnique uniq))

      go :: InterpreterFor (Meta metaeff) (MetaRun ': r)
      go = interpretViaHandlerSlow \hs w c -> case w of
          Sent (MetaMetaRun uniq' (MetaRun effUniq _)) _ ->
            bomb uniq' effUniq
          Weaved (MetaMetaRun uniq' (MetaRun effUniq _)) _ _ _ _ ->
            bomb uniq' effUniq
          Sent (SendMeta (metaeff :: metaeff l z _x) to1 to2) n ->
            let
              handleHandlingMetaSpecific
                :: forall q x. HandlingMeta metaeff Identity r l q x -> x
              handleHandlingMetaSpecific = \case
                ProcessMeta pr (Identity x) ex -> do
                  effUniq <- newUniqueSem
                  n (to2 uniq effUniq pr (ex x))
                    & go_
                    & exposeMetaRun Here effUniq
                    & rewriteAt (SCons SEnd) HandlingMetaMetaRun
                    &# fmap Identity
                ProcessMeta' pr (Identity x) ex -> do
                  effUniq <- newUniqueSem
                  n (to2 uniq effUniq pr (ex x))
                    & exposeMetaRun (There Here) effUniq
                    & rewriteAt (SCons (SCons SEnd)) HandlingMetaMetaRun
                    &# fmap Identity
                _ -> errorWithoutStackTrace
                      "handleHandlingMetaSpecific: not specially handled"
              -- {-# INLINE handleHandlingMetaSpecific #-}

              goSent :: forall rC x mh
                      . mh ~ HandlingMeta metaeff Identity r l
                     => Sem (HigherOrder z Identity (Meta metaeff)
                              (mh ': r) rC ': rC) x
                     -> Sem rC x
              goSent = interpretViaHandlerFast $ \n' hs' ->
                let
                  k' = Handlers n' hs'
                in \wav c' -> fromFOEff wav $ \ex' -> \case
                  GetInterpreterH -> c' $ ex' $
                    InterpreterH (rewrite HandlingMetaMetaRun
                                  . go_
                                  . handlingMetaToMeta
                                      handleHandlingMetaSpecific)
                  GetProcessorH -> c' $ ex' $
                    ProcessorH $ \(Identity t) fz ->
                      (fmap Identity
                       #. rewriteAt (SCons SEnd) HandlingMetaMetaRun
                       . n . to1 . fz) t
                  RestoreH (Identity a) -> c' $ ex' a
                  LiftWithH main -> c' $ ex' $ main $ fmap Identity #. goSent_
                  EmbedH m' -> runSem m' k' (c' . ex')
                  GetStateH -> c' $ ex' $ Identity ()
                  PropagateH pr e' n'' ->
                    getHandler k' pr
                       (mkWVia (fmap runIdentity #. n'' id .# Identity) e')
                       (c' . ex')
              -- {-# INLINE goSent #-}

              goSent_ :: forall rC x mh
                       . mh ~ HandlingMeta metaeff Identity r l
                      => Sem (HigherOrder z Identity (Meta metaeff)
                               (mh ': r) rC ': rC) x
                      -> Sem rC x
              goSent_ = goSent
              {-# NOINLINE goSent_ #-}

            in
              runSem (handlingMetaIntoMetaRun handleHandlingMetaSpecific
                        (goSent (h metaeff))) hs c
          Weaved (SendMeta (metaeff :: metaeff l z _x) to1 to2)
                  (trav :: Traversal t) _ wv lwr ->
            reify trav $ \(_ :: pr s) ->
              let
                handleHandlingMetaSpecific
                  :: forall q x
                   . HandlingMeta metaeff (ViaTraversal s t) r l q x -> x
                handleHandlingMetaSpecific = \case
                  ProcessMeta pr t ex' -> do
                    effUniq <- newUniqueSem
                    wv (getViaTraversal (fmap (to2 uniq effUniq pr . ex') t))
                      & go_
                      & exposeMetaRun Here effUniq
                      & rewriteAt (SCons SEnd) HandlingMetaMetaRun
                      &# fmap ViaTraversal
                  ProcessMeta' pr t ex' -> do
                    effUniq <- newUniqueSem
                    wv (getViaTraversal (fmap (to2 uniq effUniq pr . ex') t))
                      & exposeMetaRun (There Here) effUniq
                      & rewriteAt (SCons (SCons SEnd)) HandlingMetaMetaRun
                      &# fmap ViaTraversal
                  _ -> errorWithoutStackTrace
                        "handleHandlingMetaSpecific: not specially handled"
                -- {-# INLINE handleHandlingMetaSpecific #-}

                goWeaved :: forall rC x mh
                        . mh ~ HandlingMeta metaeff (ViaTraversal s t) r l
                       => Sem (HigherOrder z (ViaTraversal s t) (Meta metaeff)
                                (mh ': r) rC ': rC) x
                       -> Sem (Weave t rC ': rC) x
                goWeaved = reinterpretViaHandlerFast $ \_ hs' ->
                  let
                    AHandler !wH = AHandler $ getHandler' hs' Here
                  in
                    \wav' c' -> fromFOEff wav' $ \ex' -> \case
                      GetInterpreterH -> c' $ ex' $
                        InterpreterH (rewrite HandlingMetaMetaRun
                                      . go_
                                      . handlingMetaToMeta
                                          handleHandlingMetaSpecific)
                      GetProcessorH ->
                          c' $ ex' $ ProcessorH $ \t fz ->
                            (fmap ViaTraversal
                             #. rewriteAt (SCons SEnd) HandlingMetaMetaRun
                             . wv
                             .# getViaTraversal) (fmap (to1 . fz) t)
                      RestoreH (ViaTraversal t) ->
                        wH (mkW (RestoreW t)) (c' . ex')
                      LiftWithH main ->
                        (`wH` c') $ mkW $ LiftWithW $ \lwr' ->
                          ex' $ main $ (fmap ViaTraversal #. lwr' . goWeaved_)
                      EmbedH m' -> wH (mkW $ EmbedW m') (c' . ex')
                      GetStateH ->
                        wH (mkW (GetStateW (\w -> ViaTraversal (w ()))))
                           (c' . ex')
                      PropagateH pr e' n ->
                        (`wH` id) $ mkW $ GetStateW $ \mkS' ->
                        (`wH` id) $ mkW $ LiftWithW $ \lwr' ->
                        wH (mkW (
                               EmbedW $ liftWeaving pr
                               $ Weaved e' trav mkS'
                                  (fmap getViaTraversal #. n id .# ViaTraversal)
                                  lwr'
                                  )) $ \ta ->
                        wH (mkW $ RestoreW ta) (c' . ex')
                -- {-# INLINE goWeaved #-}

                goWeaved_ :: forall rC x mh
                           . mh ~ HandlingMeta metaeff (ViaTraversal s t) r l
                          => Sem (HigherOrder z (ViaTraversal s t)
                                   (Meta metaeff)
                                   (mh ': r) rC ': rC) x
                          -> Sem (Weave t rC ': rC) x
                goWeaved_ = goWeaved
                {-# NOINLINE goWeaved_ #-}
              in
                runSem (handlingMetaIntoMetaRun handleHandlingMetaSpecific
                          (lwr (goWeaved (h metaeff)))) hs (c .# coerce)
      -- {-# INLINE go #-}

      go_ :: InterpreterFor (Meta metaeff) (MetaRun ': r)
      go_ = go
      {-# NOINLINE go_ #-}

  m
    & splitMeta uniq
    & go
    & interpretFast \(MetaRun effUniq _) ->
      errorWithoutStackTrace
        ("Unhandled MetaRun! Report this as a bug on the polysemy GitHub repo."
         ++ "\tWith MetaRun Unique: " ++ show (hashUnique effUniq))
  where
    handlingMetaToMeta
      :: forall t meta r' l x
       . (forall q y. HandlingMeta metaeff t r l q y -> y)
      -> Sem (meta ': HandlingMeta metaeff t r l ': r') x
      -> Sem (meta ': MetaRun ': r') x
    handlingMetaToMeta specific = goHMTM
      where
        hMTMHS :: HandlerTrans (meta ': HandlingMeta metaeff t r l ': r') (meta ': MetaRun ': r')
        hMTMHS (Handlers n hs) =
          let
            AHandler !hMR = AHandler $ getHandler' hs (There Here)

            AHandler hHM = AHandler $ \wv c -> case wv of
              Sent (HandlingMetaMetaRun metarun) n ->
                hMR (Sent metarun n) c
              Weaved (HandlingMetaMetaRun metarun) trav mkS wv lwr ->
                hMR (Weaved metarun trav mkS wv lwr) c
              _ -> fromFOEff wv $ \ex e -> c (ex (specific e))
          in
            Handlers (n . goHMTM_) $
              getHandler' hs Here `consHandler'` hHM `consHandler'`
              dropHandlers' @'[_, _] hs
        goHMTM :: forall y
                . Sem (meta ': HandlingMeta metaeff t r l ': r') y
               -> Sem (meta ': MetaRun ': r') y
        goHMTM = hoistSem hMTMHS
        -- {-# INLINE goHMTM #-}

        goHMTM_ :: forall y
                 . Sem (meta ': HandlingMeta metaeff t r l ': r') y
                -> Sem (meta ': MetaRun ': r') y
        goHMTM_ = goHMTM
        {-# NOINLINE goHMTM_ #-}
    -- {-# INLINE handlingMetaToMeta #-}

    handlingMetaIntoMetaRun
      :: forall t l r' x
       . (forall q y. HandlingMeta metaeff t r l q y -> y)
      -> Sem (HandlingMeta metaeff t r l ': r') x
      -> Sem (MetaRun ': r') x
    handlingMetaIntoMetaRun specific = goHMIMR
      where
        hMIMRHS :: HandlerTrans (HandlingMeta metaeff t r l ': r') (MetaRun ': r')
        hMIMRHS (Handlers n hs) =
          let
            AHandler !hMR = AHandler $ getHandler' hs Here
            AHandler hHM = AHandler $ \wav c -> case wav of
              Sent (HandlingMetaMetaRun metarun) n ->
                hMR (Sent metarun n) c
              Weaved (HandlingMetaMetaRun metarun) trav mkS wv lwr ->
                hMR (Weaved metarun trav mkS wv lwr) c
              _ -> fromFOEff wav $ \ex e -> c (ex (specific e))
          in
            Handlers (n . goHMIMR_) (consHandler' hHM (dropHandlers' @'[_] hs))

        goHMIMR
          :: Sem (HandlingMeta metaeff t r l ': r') y
          -> Sem (MetaRun ': r') y
        goHMIMR = hoistSem hMIMRHS
        -- {-# INLINE goHMIMR #-}

        goHMIMR_
          :: forall y
           . Sem (HandlingMeta metaeff t r l ': r') y
          -> Sem (MetaRun ': r') y
        goHMIMR_ = goHMIMR
        {-# NOINLINE goHMIMR_ #-}
    -- {-# INLINE handlingMetaIntoMetaRun #-}

{-
interpretMeta
  :: forall metaeff r
   . MetaHandler metaeff r
  -> InterpreterFor (Meta metaeff) r
interpretMeta h = \m -> do
  uniq <- newUniqueSem
  m
    & reinterpret2H \case
      MetaMetaRun uniq' metarun
        | uniq == uniq' -> propagate metarun
      other -> propagate other
    & interpretH \case
      MetaMetaRun uniq' (MetaRun effUniq _) -> errorWithoutStackTrace
        ("Stray MetaMetaRun! Report this as a bug on the polysemy GitHub repo."
         ++ "\tWith interpretMeta unique " ++ show (hashUnique uniq')
         ++ ", and with MetaRun unique " ++ show (hashUnique effUniq) ++ "\n"
         ++ "\tCurrent interpretMeta unique is " ++ show (hashUnique uniq))
      SendMeta (metaeff :: metaeff l z _x) to1 to2 -> do
        (_ :: TypeParamsH k t meta mr mr) <- getTypeParamsH
        ProcessorH prcs <- getProcessorH
        InterpreterH interp <- getInterpreterH
        let
          handlingMetaCommon :: forall q x. HandlingMeta metaeff t r l q x -> x
          handlingMetaCommon = \case
            ProcessMeta pr t ex -> do
              effUniq <- newUniqueSem
              prcs t (to2 uniq effUniq pr . ex)
                & interp
                & exposeMetaRun Here effUniq
                & rewriteAt (SCons SEnd) HandlingMetaMetaRun
            ProcessMeta' pr t ex -> do
              effUniq <- newUniqueSem
              prcs t (to2 uniq effUniq pr . ex)
                & exposeMetaRun (There Here) effUniq
                & rewriteAt (SCons (SCons SEnd)) HandlingMetaMetaRun
            _ ->
              errorWithoutStackTrace "handlingMetaCommon: Not commonly handled"

          handlingMetaToOther
            :: forall r'
             . (forall n y. MetaRun n y -> Bundle r' n y)
            -> InterpreterFor (HandlingMeta metaeff t r l) r'
          handlingMetaToOther toBdl = interpretH \case
            HandlingMetaMetaRun metarun | Bundle pr act <- toBdl metarun ->
              propagateUsing pr act
            other -> return $ handlingMetaCommon other

          rewriteHigherOrderCommon
            :: forall rA rB r' q y mh
             . mh ~ HandlingMeta metaeff t r l
            => HigherOrder z t meta (mh ': r) rA q y
            -> Sem (HigherOrder k t meta (MetaRun ': r) rB ': r') y
          rewriteHigherOrderCommon = \case
            GetProcessorH -> do
              return $ ProcessorH $ \t fz ->
                rewriteAt (SCons SEnd) HandlingMetaMetaRun $ prcs t (to1 . fz)
            GetInterpreterH -> do
              return $ InterpreterH $
                sinkBelow @'[_]
                >>> raiseUnder2
                >>> handlingMetaToOther (Bundle (There Here))
                >>> interp
                >>> rewrite HandlingMetaMetaRun
            LiftWithH main -> liftWithH $ \lwr -> return $
              main (lwr . rewriteHigherOrder)
            RestoreH t -> restoreH t
            GetStateH -> getStateH
            _ -> errorWithoutStackTrace
                  "rewriteHigherOrderCommon: not commonly handled"

          rewriteHigherOrderFirst
            :: forall r' y mh
             . mh ~ HandlingMeta metaeff t r l
            => Sem (HigherOrder z t meta (mh ': r) (mh ': r) ': r') y
            -> Sem (HigherOrder k t meta (MetaRun ': r) (MetaRun ': r) ': r') y
          rewriteHigherOrderFirst = reinterpret \case
            EmbedH m' -> embedH $
              handlingMetaToOther (Bundle Here) (raiseUnder m')
            PropagateH Here e n' -> case e of
              HandlingMetaMetaRun metarun ->
                sendUsing Here $
                  PropagateH Here metarun
                    (\ex -> handlingMetaToOther (Bundle Here) . raiseUnder
                            . n' ex)
              other -> return $ handlingMetaCommon other
            PropagateH (There pr) e n' ->
              sendUsing Here $
                PropagateH
                  (There pr)
                  e
                  (\ex -> handlingMetaToOther (Bundle Here)
                          . raiseUnder
                          . n' ex)
            e -> rewriteHigherOrderCommon e

          rewriteHigherOrder
            :: forall rC y mh
             . mh ~ HandlingMeta metaeff t r l
            => Sem (HigherOrder z t meta (mh ': r) rC ': rC) y
            -> Sem (HigherOrder k t meta (MetaRun ': r) rC ': rC) y
          rewriteHigherOrder = reinterpret \case
            EmbedH m' -> embedH m'
            PropagateH n' pr e -> sendUsing Here $ PropagateH n' pr e
            e -> rewriteHigherOrderCommon e

        h metaeff
          & (raiseUnder2 . raiseUnder2)
          & rewriteHigherOrderFirst
          & subsumeUsing (There Here)
          & handlingMetaToOther (Bundle membership)

    & interpretFast \(MetaRun effUniq _) ->
      errorWithoutStackTrace
        ("Unhandled MetaRun! Report this as a bug on the polysemy GitHub repo."
         ++ "\tWith MetaRun Unique: " ++ show (hashUnique effUniq))
-}

reinterpretMeta
  :: forall metaeff e2 r
   . MetaHandler metaeff (e2 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': r) x)
reinterpretMeta h = interpretMeta h . raiseUnder
-- {-# INLINE reinterpretMeta #-}

reinterpretMeta2
  :: forall metaeff e2 e3 r
   . MetaHandler metaeff (e2 ': e3 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': r) x)
reinterpretMeta2 h = interpretMeta h . raise2Under
-- {-# INLINE reinterpretMeta2 #-}

reinterpretMeta3
  :: forall metaeff e2 e3 e4 r
   . MetaHandler metaeff (e2 ': e3 ': e4 ': r)
  -> (forall x. Sem (Meta metaeff ': r) x -> Sem (e2 ': e3 ': e4 ': r) x)
reinterpretMeta3 h = interpretMeta h . raise3Under
-- {-# INLINE reinterpretMeta3 #-}
