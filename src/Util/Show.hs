module Util.Show where

import Data.List (intercalate)
import Data.List.Split

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

toHtmlString :: String -> String
toHtmlString = (\x -> "<br />" ++ x ++ "<br />")
               . replace "\n" "<br />"
               . replace " " "&nbsp;"

doParens :: String -> String
doParens s | ' ' `elem` s = '(' : s ++ ")"
           | otherwise    = s
