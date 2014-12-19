{-# OPTIONS_GHC -fno-warn-orphans #-}
module Util.ExceptTIsFresh where

import Control.Monad.Except
import Unbound.LocallyNameless

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh