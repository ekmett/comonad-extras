-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Store.Representable
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The representable store (state-in-context/costate) comonad transformer is 
-- subject to the laws:
-- 
-- > x = seek (pos x) x
-- > y = pos (seek y x)
-- > seek y x = seek y (seek z x)
--
-- Thanks go to Russell O'Connor and Daniel Peebles for their help formulating 
-- and proving the laws for this comonad transformer.
--
-- Representable functors are isomorphic to '(->) x' for some choice of 'x'.
-- Therefore we can use them as the backing representation for a store with
-- index 'x'!
----------------------------------------------------------------------------
module Control.Comonad.Store.Representable
  ( 
  -- * The Store comonad
    Store, store, runStore
  -- * The Store comonad transformer
  , StoreT(..), runStoreT
  -- * Operations
  , module Control.Comonad.Store.Class
  ) where

import Control.Comonad
import Control.Comonad.Hoist.Class
import Control.Comonad.Trans.Class
import Data.Functor.Identity
import Data.Functor.Adjunction

#ifdef __GLASGOW_HASKELL__
import Data.Typeable
instance (Typeable s, Typeable1 w) => Typeable1 (StoreT s w) where
  typeOf1 dswa = mkTyConApp storeTTyCon [typeOf (s dswa), typeOf1 (w dswa)]
    where
      s :: StoreT s w a -> s
      s = undefined
      w :: StoreT s w a -> w a
      w = undefined

instance (Typeable s, Typeable1 w, Typeable a) => Typeable (StoreT s w a) where
  typeOf = typeOfDefault

storeTTyCon :: TyCon
storeTTyCon = mkTyCon "Control.Comonad.Trans.Store.Strict.StoreT"
{-# NOINLINE storeTTyCon #-}
#endif

type Store g s = StoreT g s Identity

store :: Adjunction f g => (f () -> a) -> f () -> Store g (f ()) a 
store f s = StoreT r (Identity (rep r f)) s
  where r = repAdjunction 

runStore :: Store g s a -> (s -> a, s)
runStore (StoreT r (Identity f) s) = (unrep r f, s)

data StoreT s w a where
  StoreT :: Functor g => Representation g s -> w (g a) -> s -> StoreT s w a 

storeT :: Adjunction f g => w (f () -> a) -> f () -> StoreT g (f ()) w a
storeT f s = StoreT r (rep r <$> f) s where 
  r = repAdjunction

runStoreT :: StoreT g s w a -> (w (s -> a), s)
runStoreT (StoreT r wf s) = (unrep r <$> wf, s)

instance (Functor w, Functor g) => Functor (StoreT s w) where
  fmap f (StoreT wf s) = StoreT (fmap (f .) wf) s

instance Extend w => Extend (StoreT s w) where
  duplicate (StoreT wf s) = StoreT (extend StoreT wf) s
  extend f (StoreT wf s) = StoreT (extend (\wf' s' -> f (StoreT wf' s')) wf) s

instance Comonad w => Comonad (StoreT s w) where
  extract (StoreT wf s) = extract wf s

instance ComonadTrans (StoreT s) where
  lower (StoreT f s) = fmap ($s) f

instance ComonadHoist (StoreT s) where
  cohoist (StoreT f s) = StoreT (Identity (extract f)) s

-- | Read the current position
pos :: StoreT s w a -> s
pos (StoreT _ s) = s

-- | Seek to an absolute location
--
-- > seek s = peek s . duplicate
seek :: Comonad w => s -> StoreT s w a -> StoreT s w a
seek s ~(StoreT f _) = StoreT f s

-- | Seek to a relative location
--
-- > seeks f = peeks f . duplicate
seeks :: Comonad w => (s -> s) -> StoreT s w a -> StoreT s w a
seeks f ~(StoreT g s) = StoreT g (f s)

-- | Peek at a value at a given absolute location
--
-- > peek x . extend (peek y) = peek y
peek :: Comonad w => s -> StoreT s w a -> a
peek s (StoreT g _) = extract g s

-- | Peek at a value at a given relative location
peeks :: Comonad w => (s -> s) -> StoreT s w a -> a
peeks f ~(StoreT g s) = extract g (f s)

