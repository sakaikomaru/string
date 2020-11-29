{-# LANGUAGE BangPatterns #-}

module Data.String.ZAlgorithm where

import qualified Data.ByteString.Char8       as BSC8
import qualified Data.ByteString.Unsafe      as BSU
import qualified Data.Vector.Unboxed         as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

zAlgorithm :: BSC8.ByteString -> VU.Vector Int
zAlgorithm bs = VU.create $ do
  z  <- VUM.replicate n 0
  vl <- VUM.replicate 1 0
  vr <- VUM.replicate 1 0
  VU.forM_ (VU.generate n succ) $ \i -> do
    r <- VUM.unsafeRead vr 0
    if i > r
      then do
        let r' = searchR i i
        VUM.unsafeWrite z  i (r' - i)
        VUM.unsafeWrite vl 0 i
        VUM.unsafeWrite vr 0 (r' - 1)
      else do
        l <- VUM.unsafeRead vl 0
        let k = i - l
        zk <- VUM.unsafeRead z k
        if zk < r - i + 1
          then do
            VUM.unsafeWrite z i zk
          else do
            let r' = searchR i r
            VUM.unsafeWrite z i (r' - i)
            VUM.unsafeWrite vl 0 i
            VUM.unsafeWrite vr 0 (r' - 1)
  VUM.unsafeWrite z 0 n
  return z
    where
      !n = BSC8.length bs
      searchR :: Int -> Int -> Int
      searchR l = go
        where
          go !r
            | r < n, BSU.unsafeIndex bs (r - l) == BSU.unsafeIndex bs r = go (r + 1)
            | otherwise = r