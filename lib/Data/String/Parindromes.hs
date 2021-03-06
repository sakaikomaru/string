{-# LANGUAGE BangPatterns #-}

module Data.String.Parindromes where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Data.Bool
import           Data.STRef.Strict
import           Data.Word
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Unsafe            as BSU
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

manacher :: BS.ByteString -> VU.Vector Int
manacher bs = VU.create $ do
  rad <- VUM.replicate n 0
  fix `flip` 0 `flip` 0 $ \loop !center !radius -> do
    when (center < n) $ do
      let !radius' = naiveRadius center radius
      VUM.unsafeWrite rad center radius'
      flip fix 1 $ \inner !r -> do
        if center >= r && center + r < n
          then do
            radL <- VUM.unsafeRead rad (center - r)
            if r + radL < radius'
              then do
                VUM.unsafeWrite rad (center + r) radL
                inner (r + 1)
              else loop (center + r) (radius' - r)
          else loop (center + r) (radius' - r)
  return rad
  where
    !n = BS.length bs
    naiveRadius :: Int -> Int -> Int
    naiveRadius c r = go r
      where
        go !i
          | c - i >= 0, c + i < n
          , BSU.unsafeIndex bs (c - i) == BSU.unsafeIndex bs (c + i) = go (i + 1)
          | otherwise = i

parindromes :: VU.Vector Word8 -> ST s (VU.Vector Int, VU.Vector Int)
parindromes bs = do
  let !n = VU.length bs
  p1 <- VUM.replicate (n + 1) 0 :: ST s (VUM.STVector s Int)
  p2 <- VUM.replicate n 0 :: ST s (VUM.STVector s Int)
  rep 2 $ \z -> do
    let zz = bool 1 0 (z == 1)
    lRef <- newSTRef (0 :: Int)
    rRef <- newSTRef (0 :: Int)
    rep n $ \i -> do
      l <- readSTRef lRef
      r <- readSTRef rRef
      let t = r - i + zz
      when (i < r) $ do
        if z == 0
          then do
            item <- VUM.unsafeRead p1 (l + t)
            VUM.unsafeWrite p1 i (min t item)
          else do
            item <- VUM.unsafeRead p2 (l + t)
            VUM.unsafeWrite p2 i (min t item)
      if z == 0
        then do
          item  <- VUM.unsafeRead p1 i
          llRef <- newSTRef (i - item)
          rrRef <- newSTRef (i + item - zz)
          fix $ \loop -> do
            ll <- readSTRef llRef
            rr <- readSTRef rrRef
            let
              sl = bs VU.! (ll - 1)
              sr = bs VU.! (rr + 1)
            when (ll /= 0 && rr + 1 < n && sl == sr) $ do
              VUM.unsafeModify p1 succ i
              modifySTRef llRef pred
              modifySTRef rrRef succ
              loop
          ll <- readSTRef llRef
          rr <- readSTRef rrRef
          when (rr > r) $ do
            writeSTRef lRef ll
            writeSTRef rRef rr
        else do
          item  <- VUM.unsafeRead p2 i
          llRef <- newSTRef (i - item)
          rrRef <- newSTRef (i + item - zz)
          fix $ \loop -> do
            ll <- readSTRef llRef
            rr <- readSTRef rrRef
            let
              sl = bs VU.! (ll - 1)
              sr = bs VU.! (rr + 1)
            when (ll /= 0 && rr + 1 < n && sl == sr) $ do
              VUM.unsafeModify p2 succ i
              modifySTRef llRef pred
              modifySTRef rrRef succ
              loop
          ll <- readSTRef llRef
          rr <- readSTRef rrRef
          when (rr > r) $ do
            writeSTRef lRef ll
            writeSTRef rRef rr
  target1 <- VU.unsafeFreeze p1
  target2 <- VU.unsafeFreeze p2
  return (VU.tail target1, target2)

enumParindromes :: VU.Vector Word8 -> VU.Vector Int
enumParindromes bs = VU.create $ do
  let !n = VU.length bs
  (_even, _odd) <- parindromes bs
  res <- VUM.unsafeNew (2 * n - 1) :: ST s (VUM.STVector s Int)
  rep (2 * n - 1) $ \i -> do
    if even i
      then VUM.unsafeWrite res i (2 * _odd VU.! (i `div` 2) + 1)
      else VUM.unsafeWrite res i (2 * _even VU.! (i `div` 2))
  return res

-------------------------------------------------------------------------------
-- for
-------------------------------------------------------------------------------
rep :: Monad m => Int -> (Int -> m ()) -> m ()
rep n = flip VFSM.mapM_ (stream 0 n)
{-# INLINE rep #-}

rep' :: Monad m => Int -> (Int -> m ()) -> m ()
rep' n = flip VFSM.mapM_ (stream 0 (n + 1))
{-# INLINE rep' #-}

rep1 :: Monad m => Int -> (Int -> m ()) -> m ()
rep1 n = flip VFSM.mapM_ (stream 1 n)
{-# INLINE rep1 #-}

rep1' :: Monad m => Int -> (Int -> m ()) -> m ()
rep1' n = flip VFSM.mapM_ (stream 1 (n + 1))
{-# INLINE rep1' #-}

rev :: Monad m => Int -> (Int -> m ()) -> m ()
rev n = flip VFSM.mapM_ (streamR 0 n)
{-# INLINE rev #-}

rev' :: Monad m => Int -> (Int -> m ()) -> m ()
rev' n = flip VFSM.mapM_ (streamR 0 (n + 1))
{-# INLINE rev' #-}

rev1 :: Monad m => Int -> (Int -> m ()) -> m ()
rev1 n = flip VFSM.mapM_ (streamR 1 n)
{-# INLINE rev1 #-}

rev1' :: Monad m => Int -> (Int -> m ()) -> m ()
rev1' n = flip VFSM.mapM_ (streamR 1 (n + 1))
{-# INLINE rev1' #-}

range :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
range l r = flip VFSM.mapM_ (stream l (r + 1))
{-# INLINE range #-}

rangeR :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
rangeR r l = flip VFSM.mapM_ (streamR l (r + 1))
{-# INLINE rangeR #-}

forStep :: Monad m => Int -> Int -> Int -> (Int -> m ()) -> m ()
forStep l r d = flip VFSM.mapM_ (streamStep l r d)
{-# INLINE forStep #-}

forStepR :: Monad m => Int -> Int -> Int -> (Int -> m ()) -> m ()
forStepR r l d = flip VFSM.mapM_ (streamStepR l r d)
{-# INLINE forStepR #-}

forP :: Monad m => Int -> (Int -> m ()) -> m ()
forP p = flip VFSM.mapM_ (streamG 2 p (^) 2 (+) 1)
{-# INLINE forP #-}

forG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forG l r f p g d = flip VFSM.mapM_ (streamG l r f p g d)
{-# INLINE forG #-}

forRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forRG r l f p g d = flip VFSM.mapM_ (streamRG r l f p g d)
{-# INLINE forRG #-}

stream :: Monad m => Int -> Int -> VFSM.Stream m Int
stream !l !r = VFSM.Stream step l
  where
    step x
      | x < r     = return $ VFSM.Yield x (x + 1)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] stream #-}

streamR :: Monad m => Int -> Int -> VFSM.Stream m Int
streamR !l !r = VFSM.Stream step (r - 1)
  where
    step x
      | x >= l = return $ VFSM.Yield x (x - 1)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamR #-}

streamStep :: Monad m => Int -> Int -> Int -> VFSM.Stream m Int
streamStep !l !r !d = VFSM.Stream step l
  where
    step x
      | x <= r    = return $ VFSM.Yield x (x + d)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamStep #-}

streamStepR :: Monad m => Int -> Int -> Int -> VFSM.Stream m Int
streamStepR !l !r !d = VFSM.Stream step r
  where
    step x
      | x >= l    = return $ VFSM.Yield x (x - d)
      | otherwise = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamStepR #-}

streamG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> VFSM.Stream m Int
streamG !l !r !f !p !g !d = VFSM.Stream step l
  where
    step x
      | f x p <= r = return $ VFSM.Yield x (g x d)
      | otherwise  = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamG #-}

streamRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> VFSM.Stream m Int
streamRG !r !l !f !p !g !d = VFSM.Stream step r
  where
    step x
      | f x p >= l = return $ VFSM.Yield x (g x d)
      | otherwise  = return VFSM.Done
    {-# INLINE [0] step #-}
{-# INLINE [1] streamRG #-}

withBreakIO :: ((r -> ContT r IO b) -> ContT r IO r) -> IO r
withBreakIO = flip runContT pure . callCC
{-# INLINE withBreakIO #-}

withBreakST :: ((r -> ContT r (ST s) b) -> ContT r (ST s) r) -> (ST s) r
withBreakST = flip runContT pure . callCC
{-# INLINE withBreakST #-}
