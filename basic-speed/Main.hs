{-# LANGUAGE TypeApplications #-}
module Main where
import System.Random
import Basic
import Data.Sequence (index, fromList)
import qualified Data.Sequence as S
-- import Data.Foldable (sum)

main :: IO ()
main = do
  input <- newStdGen >>= \gen -> pure $ fromList $ fst $ uniformList @Int (10 ^ (7 :: Int)) gen
  sorted <- newStdGen >>= \gen -> pure $ incSort gen input
--  print $ sorted `index` (5 * 10 ^ (6 :: Int))
  print $ sum sorted
--  print $ sorted == S.sort input
