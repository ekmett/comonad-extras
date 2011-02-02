{-# LANGUAGE CPP, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Trans.Traced
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The trace comonad transformer (aka the cowriter or exponential comonad transformer).
--
----------------------------------------------------------------------------
module Control.Comonad.Traced.MemoTrie
  ( 
  -- * Traced comonad
    Traced
  , traced
  , runTraced
  -- * Traced comonad transformer
  , TracedT(..)
  -- * Operations
  , trace
  , listen
  , listens
  , censor
  ) where

import Control.Applicative
import Control.Monad.Instances
import Control.Comonad
import Control.Comonad.Hoist.Class
import Control.Comonad.Trans.Class
import Control.Comonad.Store.Class
import Control.Comonad.Env.Class
import Control.Comonad.Traced.Class
import Data.Functor
import Data.Functor.Apply
import Data.Functor.Identity
import Data.Monoid
import Data.Semigroup
import Data.MemoTrie

import Data.Typeable

type Traced m = TracedT m Identity

traced :: HasTrie m => (m -> a) -> Traced m a
traced = TracedT . Identity . trie

runTraced :: HasTrie m => Traced m a -> m -> a
runTraced = untrie . runIdentity . untracedT 

newtype TracedT m w a = TracedT (w (m :->: a))

untracedT :: TracedT m w a -> w (m :->: a)
untracedT (TracedT wf) = wf

runTracedT :: (Functor w, HasTrie m) => TracedT m w a -> w (m -> a)
runTracedT = fmap untrie . untracedT 

tracedT :: (Functor w, HasTrie m) => w (m -> a) -> TracedT m w a
tracedT = TracedT . fmap trie

instance (Functor w, HasTrie m) => Functor (TracedT m w) where
  fmap g = TracedT . fmap (fmap g) . untracedT

instance (Apply w, HasTrie m) => Apply (TracedT m w) where
  TracedT wf <.> TracedT wa = TracedT ((<*>) <$> wf <.> wa)

instance (Applicative w, HasTrie m) => Applicative (TracedT m w) where
  pure = TracedT . pure . pure
  TracedT wf <*> TracedT wa = TracedT ((<*>) <$> wf <*> wa)

instance (Extend w, Semigroup m, HasTrie m) => Extend (TracedT m w) where
  extend f = TracedT 
           . extend (trie . (\wf m -> f (TracedT (inTrie (. (<>) m) <$> wf)))) 
           . untracedT

instance (Comonad w, Semigroup m, Monoid m, HasTrie m) => Comonad (TracedT m w) where
  extract (TracedT wf) = untrie (extract wf) mempty

instance (Semigroup m, Monoid m, HasTrie m) => ComonadTrans (TracedT m) where
  lower = fmap (`untrie` mempty) . untracedT

instance (Semigroup m, Monoid m, HasTrie m) => ComonadHoist (TracedT m) where
  cohoist = TracedT . Identity . extract . untracedT

instance (ComonadStore s w, Semigroup m, Monoid m, HasTrie m) => ComonadStore s (TracedT m w) where
  pos = pos . lower
  peek s = peek s . lower

instance (Comonad w, Semigroup m, Monoid m, HasTrie m) => ComonadTraced m (TracedT m w) where
  trace m (TracedT wf) = untrie (extract wf) m

instance (ComonadEnv e w, Semigroup m, Monoid m, HasTrie m) => ComonadEnv e (TracedT m w) where
  ask = ask . lower 

-- TODO: handle these more efficiently
listen :: (Functor w, HasTrie m) => TracedT m w a -> TracedT m w (a, m)
listen = tracedT . fmap (\f m -> (f m, m)) . runTracedT

listens :: (Functor w, HasTrie m) => (m -> b) -> TracedT m w a -> TracedT m w (a, b)
listens g = tracedT . fmap (\f m -> (f m, g m)) . runTracedT 

censor :: (Functor w, HasTrie m) => (m -> m) -> TracedT m w a -> TracedT m w a
censor g = tracedT . fmap (. g) . runTracedT

#ifdef __GLASGOW_HASKELL__

instance (Typeable s, Typeable1 w) => Typeable1 (TracedT s w) where
  typeOf1 dswa = mkTyConApp tracedTTyCon [typeOf (s dswa), typeOf1 (w dswa)]
    where
      s :: TracedT s w a -> s
      s = undefined
      w :: TracedT s w a -> w a
      w = undefined

tracedTTyCon :: TyCon
tracedTTyCon = mkTyCon "Control.Comonad.Trans.Traced.TracedT"
{-# NOINLINE tracedTTyCon #-}

#endif
