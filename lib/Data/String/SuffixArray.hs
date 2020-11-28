{-# LANGUAGE BangPatterns #-}

module Data.String.SuffixArray where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Data.Bool
import           Data.IORef
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

inducedSort :: VU.Vector Int -> Int -> VUM.IOVector Int -> VU.Vector Bool -> VU.Vector Int -> IO ()
inducedSort vec valRange sa sl lmsIdx = do
  l <- VUM.unsafeNew valRange :: IO (VUM.IOVector Int)
  r <- VUM.unsafeNew valRange :: IO (VUM.IOVector Int)
  VU.forM_ vec $ \c -> do
    when (c + 1 < valRange) $ VUM.unsafeModify l succ (c + 1)
    VUM.unsafeModify r succ c
  rep1 (VUM.length l) $ \i -> do
    item <- VUM.unsafeRead l (i - 1)
    VUM.unsafeModify l (+ item) i
  rep1 (VUM.length r) $ \i -> do
    item <- VUM.unsafeRead r (i - 1)
    VUM.unsafeModify r (+ item) i
  rep (VUM.length sa) $ \i -> VUM.unsafeWrite sa i (-1)
  rev (VU.length lmsIdx) $ \i -> do
    let idxteriwh = vec VU.! (lmsIdx VU.! i)
    VUM.unsafeModify r pred idxteriwh
    item <- VUM.unsafeRead r idxteriwh
    VUM.unsafeWrite sa item (lmsIdx VU.! i)
  rep (VUM.length sa) $ \idx -> do
    i <- VUM.unsafeRead sa idx
    when (i >= 1 && sl VU.! (i - 1)) $ do
      item <- VUM.unsafeRead l (vec VU.! (i - 1))
      VUM.unsafeWrite sa item (i - 1)
      VUM.unsafeModify l succ (vec VU.! (i - 1))
  rep (VUM.length r) $ \i -> VUM.unsafeWrite r i 0
  VU.forM_ vec $ \c -> VUM.unsafeModify r succ c
  rep1 (VUM.length r) $ \i -> do
    item <- VUM.unsafeRead r (i - 1)
    VUM.unsafeModify r (+ item) i
  rev1 (VUM.length sa) $ \k -> do
    i <- VUM.unsafeRead sa k
    when (i >= 1 && not (sl VU.! (i - 1))) $ do
      VUM.unsafeModify r pred (vec VU.! (i - 1))
      rveci <- VUM.unsafeRead r (vec VU.! (i - 1))
      VUM.unsafeWrite sa rveci (i - 1)

sais :: VU.Vector Int -> Int -> IO (VUM.IOVector Int)
sais vec valRange = do
  undefined

suffixArray :: VU.Vector Char -> Int -> IO (VUM.IOVector Int)
suffixArray s lim = undefined

longestCommonPrefix :: VU.Vector Char -> VU.Vector Int -> IO (VUM.IOVector Int)
longestCommonPrefix s sa = do
  let !n = VU.length s
  kPtr <- newIORef (0 :: Int)
  lcp <- VUM.unsafeNew n  :: IO (VUM.IOVector Int)
  rank <- VUM.unsafeNew n :: IO (VUM.IOVector Int)
  rep n $ \i -> VUM.unsafeWrite rank (sa VU.! i) i
  rep n $ \i -> do
    modifyIORef kPtr (\l -> bool 0 (l - 1) (l /= 0))
    ranki <- VUM.unsafeRead rank i
    if ranki == n - 1
      then do
        writeIORef kPtr 0
      else do
        let j = sa VU.! (ranki + 1)
        fix $ \loop -> do
          k <- readIORef kPtr
          when (i + k < n && j + k < n && s VU.! (i + k) == s VU.! (j + k)) $ do
            modifyIORef' kPtr succ
            loop
        VUM.unsafeWrite lcp ranki =<< readIORef kPtr
  VUM.unsafeWrite lcp (n - 1) 0
  return lcp
-------------------------------------------------------------------------------
-- for
-------------------------------------------------------------------------------
rep :: Monad m => Int -> (Int -> m ()) -> m ()
rep n = flip VFSM.mapM_ (streamG 0 (n - 1) const 0 (+) 1)
{-# INLINE rep #-}

rep' :: Monad m => Int -> (Int -> m ()) -> m ()
rep' n = flip VFSM.mapM_ (streamG 0 n const 0 (+) 1)
{-# INLINE rep' #-}

rep1 :: Monad m => Int -> (Int -> m ()) -> m ()
rep1 n = flip VFSM.mapM_ (streamG 1 (n - 1) const 0 (+) 1)
{-# INLINE rep1 #-}

rep1' :: Monad m => Int -> (Int -> m ()) -> m ()
rep1' n = flip VFSM.mapM_ (streamG 1 n const 0 (+) 1)
{-# INLINE rep1' #-}

rev :: Monad m => Int -> (Int -> m ()) -> m ()
rev n = flip VFSM.mapM_ (streamRG (n - 1) 0 const 0 (-) 1)
{-# INLINE rev #-}

rev' :: Monad m => Int -> (Int -> m ()) -> m ()
rev' n = flip VFSM.mapM_ (streamRG n 0 const 0 (-) 1)
{-# INLINE rev' #-}

rev1 :: Monad m => Int -> (Int -> m ()) -> m ()
rev1 n = flip VFSM.mapM_ (streamRG (n - 1) 1 const 0 (-) 1)
{-# INLINE rev1 #-}

rev1' :: Monad m => Int -> (Int -> m ()) -> m ()
rev1' n = flip VFSM.mapM_ (streamRG n 1 const 0 (-) 1)
{-# INLINE rev1' #-}

range :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
range l r = flip VFSM.mapM_ (streamG l r const 0 (+) 1)
{-# INLINE range #-}

rangeR :: Monad m => Int -> Int -> (Int -> m ()) -> m ()
rangeR r l = flip VFSM.mapM_ (streamRG r l const 0 (-) 1)
{-# INLINE rangeR #-}

forP :: Monad m => Int -> (Int -> m ()) -> m ()
forP p = flip VFSM.mapM_ (streamG 2 p (^) 2 (+) 1)
{-# INLINE forP #-}

forG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forG l r f p g d = flip VFSM.mapM_ (streamG l r f p g d)
{-# INLINE forG #-}

forRG :: Monad m => Int -> Int -> (Int -> Int -> Int) -> Int -> (Int -> Int -> Int) -> Int -> (Int -> m ()) -> m ()
forRG r l f p g d = flip VFSM.mapM_ (streamRG r l f p g d)
{-# INLINE forRG #-}

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