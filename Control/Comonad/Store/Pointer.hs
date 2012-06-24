{-# LANGUAGE CPP, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Store.Pointer
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- The array-backed store (state-in-context/costate) comonad transformer is
-- subject to the laws:
--
-- > x = seek (pos x) x
-- > y = pos (seek y x)
-- > seek y x = seek y (seek z x)
--
-- Thanks go to Russell O'Connor and Daniel Peebles for their help
-- formulating and proving the laws for this comonad transformer.
--
-- This basic version of this transformer first appeared on Dan Piponi's blog
-- at <http://blog.sigfpe.com/2008/03/comonadic-arrays.html>.
--
-- Since this module relies on the non-Haskell 98 'arrays' package, it is
-- located here instead of in comonad-transformers.
--
-- NB: attempting to seek or peek out of bounds will yield an error.
----------------------------------------------------------------------------
module Control.Comonad.Store.Pointer
  (
  -- * The Pointer comonad
    Pointer, pointer, runPointer
  -- * The Pointer comonad transformer
  , PointerT(..), runPointerT
  , pointerBounds
  , module Control.Comonad.Store.Class
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Hoist.Class
import Control.Comonad.Trans.Class
import Control.Comonad.Store.Class
import Control.Comonad.Traced.Class
import Control.Comonad.Env.Class
import Data.Functor.Identity
import Data.Array

#ifdef __GLASGOW_HASKELL__
import Data.Typeable
instance (Typeable i, Typeable1 w) => Typeable1 (PointerT i w) where
  typeOf1 diwa = mkTyConApp storeTTyCon [typeOf (i diwa), typeOf1 (w diwa)]
    where
      i :: PointerT i w a -> i
      i = undefined
      w :: PointerT i w a -> w a
      w = undefined

instance (Typeable i, Typeable1 w, Typeable a) => Typeable (PointerT i w a) where
  typeOf = typeOfDefault

storeTTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
storeTTyCon = mkTyCon "Control.Comonad.Trans.Store.Pointer.PointerT"
#else
storeTTyCon = mkTyCon3 "comonad-extras" "Control.Comonad.Trans.Store.Pointer" "PointerT"
#endif
{-# NOINLINE storeTTyCon #-}
#endif

type Pointer i = PointerT i Identity

pointer :: Array i a -> i -> Pointer i a
pointer f i = PointerT (Identity f) i

runPointer :: Pointer i a -> (Array i a, i)
runPointer (PointerT (Identity f) i) = (f, i)

data PointerT i w a = PointerT (w (Array i a)) i

runPointerT :: PointerT i w a -> (w (Array i a), i)
runPointerT (PointerT g i) = (g, i)

instance (Functor w, Ix i) => Functor (PointerT i w) where
  fmap f (PointerT g i) = PointerT (fmap f <$> g) i

instance (Comonad w, Ix i) => Extend (PointerT i w) where
  duplicate (PointerT g i) = PointerT (extend p g) i where
    p wa = listArray b $ PointerT wa <$> range b where
      b = bounds (extract wa)

instance (Comonad w, Ix i) => Comonad (PointerT i w) where
  extract (PointerT g i) = extract g ! i

instance Ix i => ComonadTrans (PointerT i) where
  lower (PointerT g i) = fmap (! i) g

instance Ix i => ComonadHoist (PointerT i) where
  cohoist (PointerT g i) = PointerT (Identity (extract g)) i

instance (Comonad w, Ix i) => ComonadStore i (PointerT i w) where
  pos (PointerT _ i) = i
  seek i (PointerT g _) = PointerT g i
  seeks f (PointerT g i) = PointerT g (f i)
  peek i (PointerT g _) = extract g ! i
  peeks f (PointerT g i) = extract g ! f i
  experiment f (PointerT g i) = fmap (extract g !) (f i)

-- | Extract the bounds of the currently focused array
pointerBounds :: (Comonad w, Ix i) => PointerT i w a -> (i,i)
pointerBounds (PointerT g _) = bounds (extract g)

instance (ComonadTraced m w, Ix i) => ComonadTraced m (PointerT i w) where
  trace m = trace m . lower

instance (ComonadEnv m w, Ix i)  => ComonadEnv m (PointerT i w) where
  ask = ask . lower

