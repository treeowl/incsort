{-# LANGUAGE TypeApplications #-}
module Main where
import System.Random
import Data.Sequence (index, fromList)
import qualified Data.Sequence as S

main :: IO ()
main = do
  input <- newStdGen >>= \gen -> pure $ fromList $ fst $ uniformList @Int (10 ^ (6 :: Int)) gen
  let sorted = S.sort input
  --print $ sorted `index` (5 * 10 ^ (5 :: Int))
  print $ sum sorted
