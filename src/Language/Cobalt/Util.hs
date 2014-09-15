{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Cobalt.Util where

import Control.Monad.Except
import Data.List (intercalate)
import Data.List.Split
import Unbound.LocallyNameless

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh

replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace old new l = intercalate new . splitOn old $ l

withGreek :: String -> String
withGreek = replace "alpha" "α"
            . replace "beta" "β"
            . replace "tau" "τ"
            . replace "->" "→"
            . replace "=>" "⟹"

showWithGreek :: Show a => a -> String
showWithGreek = withGreek . show
