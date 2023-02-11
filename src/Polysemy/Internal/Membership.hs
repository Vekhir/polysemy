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
module Polysemy.Internal.Membership
  ( ElemOf(.., Here, There)
  , sameMember
  , absurdMembership
  , isMemberAt
  , memberAt
  , swapStacks
  , splitMembership
  , injectMembership
  , underMembership
  , extendMembershipLeft
  , extendMembershipRight
  , Member(..)
  , KnownRow
  , tryMembership
  ) where

import Polysemy.Internal.Sing
import Data.Typeable
import Data.Coerce
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fix
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Traversable
import Data.Type.Equality
import Data.Kind
import Polysemy.Internal.Kind
import Polysemy.Internal.Opaque
import Unsafe.Coerce
import GHC.Exts (considerAccessible)

------------------------------------------------------------------------------
-- | A proof that @e@ is an element of @r@.
--
-- Due to technical reasons, @'ElemOf' e r@ is not powerful enough to
-- prove @'Member' e r@; however, it can still be used send actions of @e@
-- into @r@ by using 'Polysemy.Internal.subsumeUsing'.
--
-- @since 1.3.0.0
type role ElemOf nominal nominal
newtype ElemOf (e :: k) (r :: [k]) = UnsafeMkElemOf Int

data MatchHere e r where
  MHYes :: MatchHere e (e ': r)
  MHNo  :: MatchHere e r

data MatchThere e r where
  MTYes :: ElemOf e r -> MatchThere e (e' ': r)
  MTNo  :: MatchThere e r

matchHere :: forall e r. ElemOf e r -> MatchHere e r
matchHere (UnsafeMkElemOf 0) = unsafeCoerce $ MHYes
matchHere _ = MHNo
{-# INLINE matchHere #-}

matchThere :: forall e r. ElemOf e r -> MatchThere e r
matchThere (UnsafeMkElemOf 0) = MTNo
matchThere (UnsafeMkElemOf e) = unsafeCoerce $ MTYes $ UnsafeMkElemOf $ e - 1
{-# INLINE matchThere #-}

absurdMembership :: ElemOf e '[] -> b
absurdMembership !_
  | considerAccessible = errorWithoutStackTrace "bad use of UnsafeMkElemOf"

pattern Here :: () => ((e ': r') ~ r) => ElemOf e r
pattern Here <- (matchHere -> MHYes)
  where
    Here = UnsafeMkElemOf 0

pattern There :: () => ((e' ': r) ~ r') => ElemOf e r -> ElemOf e r'
pattern There e <- (matchThere -> MTYes e)
  where
    There (UnsafeMkElemOf e) = UnsafeMkElemOf $ e + 1

{-# COMPLETE Here, There #-}

------------------------------------------------------------------------------
-- | Checks if two membership proofs are equal. If they are, then that means
-- that the effects for which membership is proven must also be equal.
sameMember :: forall e e' r
            . ElemOf e r
           -> ElemOf e' r
           -> Maybe (e :~: e')
sameMember (UnsafeMkElemOf i) (UnsafeMkElemOf j)
  | i == j    = Just (unsafeCoerce Refl)
  | otherwise = Nothing

isMemberAt :: forall r e e'' l e'
            . SList l
           -> ElemOf e' (Append l (e ': r))
           -> Either (ElemOf e' (Append l (e'' ': r))) (e :~: e')
isMemberAt (UnsafeMkSList i) (UnsafeMkElemOf j)
  | i == j    = Right (unsafeCoerce Refl)
  | otherwise = Left (UnsafeMkElemOf j)

memberAt :: forall r e l. SList l -> ElemOf e (Append l (e ': r))
memberAt (UnsafeMkSList i) = UnsafeMkElemOf i

------------------------------------------------------------------------------
-- | This class indicates that an effect must be present in the caller's stack.
-- It is the main mechanism by which a program defines its effect dependencies.
class Member (t :: Effect) (r :: EffectRow) where
  -- | Create a proof that the effect @t@ is present in the effect stack @r@.
  membership :: ElemOf t r

instance {-# OVERLAPPING #-} Member t (t ': z) where
  membership = Here
  {-# INLINE membership #-}

instance Member t z => Member t (_1 ': z) where
  membership = There $ membership @t @z
  {-# INLINE membership #-}

instance {-# INCOHERENT #-} Member t z => Member t (Opaque q ': z) where
  membership = There $ membership @t @z
  {-# INLINE membership #-}

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

underMembership :: forall r r' l e
                 . SList l
                -> (ElemOf e r -> ElemOf e r')
                -> ElemOf e (Append l r) -> ElemOf e (Append l r')
underMembership (UnsafeMkSList l) t = \case
  UnsafeMkElemOf pr
    | pr < l -> UnsafeMkElemOf pr
    | UnsafeMkElemOf pr' <- t (UnsafeMkElemOf (pr - l)) -> UnsafeMkElemOf (l + pr')

splitMembership :: forall right left e
                 . SList left
                -> ElemOf e (Append left right)
                -> Either (ElemOf e left) (ElemOf e right)
splitMembership (UnsafeMkSList l) (UnsafeMkElemOf pr)
  | pr < l    = Left (UnsafeMkElemOf pr)
  | otherwise = Right $! UnsafeMkElemOf (pr - l)

swapStacks :: forall r l mid e
            . SList l -> SList mid -> ElemOf e (Append l (Append mid r)) -> ElemOf e (Append mid (Append l r))
swapStacks l mid = \pr -> case splitMembership @(Append mid r) l pr of
  Left pr' -> extendMembershipLeft mid (extendMembershipRight @_ @r pr')
  Right pr' -> case splitMembership @r mid pr' of
    Left pr'' -> extendMembershipRight @_ @(Append l r) pr''
    Right pr'' -> extendMembershipLeft mid (extendMembershipLeft l pr'')
{-# INLINE swapStacks #-}
