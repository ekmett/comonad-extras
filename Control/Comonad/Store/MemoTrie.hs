{-# LANGUAGE CPP, TypeOperators, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Store.MemoTrie
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The trie-memoizing store (state-in-context/costate) comonad transformer is 
-- subject to the laws:
-- 
-- > x = seek (pos x) x
-- > y = pos (seek y x)
-- > seek y x = seek y (seek z x)
--
-- Thanks go to Russell O'Connor and Daniel Peebles for their help formulating 
-- and proving the laws for this comonad transformer.
----------------------------------------------------------------------------
module Control.Comonad.Store.MemoTrie
  ( 
  -- * The Store comonad
    Store, store, runStore
  -- * The Store comonad transformer
  , StoreT(..), storeT, runStoreT
  -- * Operations
  , module Control.Comonad.Store.Class
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Hoist.Class
import Control.Comonad.Trans.Class
import Control.Comonad.Store.Class
import Control.Comonad.Env.Class
import Control.Comonad.Traced.Class
import Data.Functor.Identity
import Data.Functor.Apply
import Data.MemoTrie
import Data.Semigroup
import Data.Monoid

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

type Store s = StoreT s Identity

store :: HasTrie s => (s -> a) -> s -> Store s a 
store f s = StoreT (Identity (trie f)) s

runStore :: HasTrie s => Store s a -> (s -> a, s)
runStore (StoreT (Identity f) s) = (untrie f, s)

data StoreT s w a = StoreT (w (s :->: a)) s

storeT :: (Functor w, HasTrie s) => w (s -> a) -> s -> StoreT s w a 
storeT wf s = StoreT (trie <$> wf) s

runStoreT :: (Functor w, HasTrie s) => StoreT s w a -> (w (s -> a), s)
runStoreT (StoreT wf s) = (untrie <$> wf, s)

instance (Functor w, HasTrie s) => Functor (StoreT s w) where
  fmap f (StoreT wf s) = StoreT (fmap (fmap f) wf) s

instance (Apply w, Semigroup s, HasTrie s) => Apply (StoreT s w) where
  StoreT ff m <.> StoreT fa n = StoreT ((<*>) <$> ff <.> fa) (m <> n)

instance (Applicative w, Semigroup s, Monoid s, HasTrie s) => Applicative (StoreT s w) where
  pure a = StoreT (pure (pure a)) mempty
  StoreT ff m <*> StoreT fa n = StoreT ((<*>) <$> ff <*> fa) (m `mappend` n)

instance (Extend w, HasTrie s) => Extend (StoreT s w) where
  duplicate (StoreT wf s) = StoreT (extend (trie . StoreT) wf) s

instance (Comonad w, HasTrie s) => Comonad (StoreT s w) where
  extract (StoreT wf s) = untrie (extract wf) s

instance HasTrie s => ComonadTrans (StoreT s) where
  lower (StoreT f s) = fmap (`untrie` s) f

instance ComonadHoist (StoreT s) where
  cohoist (StoreT f s) = StoreT (Identity (extract f)) s

instance (Comonad w, HasTrie s) => ComonadStore s (StoreT s w) where
  pos (StoreT _ s) = s
  seek s (StoreT f _) = StoreT f s
  seeks f (StoreT g s) = StoreT g (f s)
  peek s (StoreT g _) = untrie (extract g) s
  peeks f (StoreT g s) = untrie (extract g) (f s)

instance (ComonadTraced m w, HasTrie s) => ComonadTraced m (StoreT s w) where
  trace m = trace m . lower

instance (ComonadEnv m w, HasTrie s) => ComonadEnv m (StoreT s w) where 
  ask = ask . lower
