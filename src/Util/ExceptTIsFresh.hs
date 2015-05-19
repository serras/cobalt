{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Util.ExceptTIsFresh where

#if MIN_VERSION_unbound(0,4,4)
#else
import Control.Monad.Except
import Unbound.LocallyNameless

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh
#endif
