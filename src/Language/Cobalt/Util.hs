{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Cobalt.Util where

import Control.Monad.Except
import Unbound.LocallyNameless

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh
