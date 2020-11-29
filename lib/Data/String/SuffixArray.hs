{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TypeApplications #-}

module Data.String.SuffixArray where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Data.Bool
import           Data.IORef
import           Data.STRef
import           Data.Word
import           Unsafe.Coerce
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

inducedSort :: VU.Vector Int -> Int -> VUM.STVector s Int -> VU.Vector Bool -> VU.Vector Int -> ST s ()
inducedSort vec valRange sa sl lmsIdx = do
  l <- VUM.unsafeNew valRange :: ST s (VUM.STVector s Int)
  r <- VUM.unsafeNew valRange :: ST s (VUM.STVector s Int)
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

sais :: VUM.STVector s Int -> Int -> ST s (VUM.STVector s Int)
sais mvec lim = do
  let !n = VUM.length mvec
  sa     <- VUM.unsafeNew n :: ST s (VUM.STVector s Int)
  lmsIdx <- VUM.unsafeNew n :: ST s (VUM.STVector s Int)
  sl0    <- VUM.unsafeNew n :: ST s (VUM.STVector s Bool)
  VUM.unsafeWrite sl0 (n - 1) False
  rangeR (n - 2) 0 $ \i -> do
    mveci  <- VUM.unsafeRead mvec i
    mveci1 <- VUM.unsafeRead mvec (i + 1)
    sli1   <- VUM.unsafeRead sl0 (i + 1)
    let sli = mveci > mveci1 || (mveci == mveci1 && sli1)
    VUM.unsafeWrite sl0 i sli
    when (sli && not sli1) $ VUM.unsafeWrite lmsIdx i (i + 1)
  lmsIDX <- VU.filter (/= 0) <$> VU.unsafeFreeze lmsIdx
  sl     <- VU.unsafeFreeze sl0
  vec    <- VU.unsafeFreeze mvec
  inducedSort vec lim sa sl lmsIDX
  let lmsidxSize = VU.length lmsIDX
  newLMSidx <- VUM.unsafeNew lmsidxSize :: ST s (VUM.STVector s Int)
  lmsVec    <- VUM.unsafeNew lmsidxSize :: ST s (VUM.STVector s Int)
  kRef <- newSTRef (0 :: Int)
  rep n $ \i -> do
    sai <- VUM.unsafeRead sa i
    when (not (sl VU.! sai) && sai >= 1 && sl VU.! (sai - 1)) $ do
      k <- readSTRef kRef
      VUM.unsafeWrite newLMSidx k sai
      modifySTRef kRef succ
  cur <- newSTRef (0 :: Int)
  VUM.unsafeWrite sa (n - 1) 0
  rep1 (VUM.length newLMSidx) $ \k -> do
    i <- VUM.unsafeRead newLMSidx (k - 1)
    j <- VUM.unsafeRead newLMSidx k
    if vec VU.! i /= vec VU.! j
      then do
        modifySTRef cur succ
        VUM.unsafeWrite sa j =<< readSTRef cur
      else do
        flag <- newSTRef False
        withBreakST $ \break -> fix (\loop a b -> do
          when (vec VU.! a /= vec VU.! b) $ do
            lift $ writeSTRef flag True
            break ()
          when ((not (sl VU.! a) && sl VU.! (a - 1)) || (not (sl VU.! b) && sl VU.! (b - 1))) $ do
            lift $ writeSTRef flag (not ((not (sl VU.! a) && sl VU.! (a - 1)) && (not (sl VU.! b) && sl VU.! (b - 1))))
            break ()
          loop (a + 1) (b + 1)
          ) (i + 1) (j + 1)
        _flag <- readSTRef flag
        _cur  <- readSTRef cur
        if _flag
          then do
            VUM.unsafeWrite sa j (_cur + 1)
            modifySTRef cur succ
          else VUM.unsafeWrite sa j _cur
  rep lmsidxSize $ \i -> do
    salmsidxi <- VUM.unsafeRead sa (lmsIDX VU.! i)
    VUM.unsafeWrite lmsVec i salmsidxi
  cur' <- readSTRef cur
  if cur' + 1 < lmsidxSize
    then do
      lm <- sais lmsVec (cur' + 1)
      rep lmsidxSize $ \i -> do
        item <- VUM.unsafeRead lm i
        VUM.unsafeWrite newLMSidx i (lmsIDX VU.! item)
      lms <- VU.unsafeFreeze newLMSidx
      inducedSort vec lim sa sl lms
      return sa
    else do
      lms <- VU.unsafeFreeze newLMSidx
      inducedSort vec lim sa sl lms
      return sa

suffixArray :: VU.Vector Word8 -> VU.Vector Int
suffixArray s = VU.create $ do
  let
    n = VU.length s + 1
  new <- VUM.unsafeNew n :: ST s (VUM.STVector s Int)
  rep n $ \i -> do
    if i == (n - 1)
      then VUM.unsafeWrite new (n - 1) 36
      else VUM.unsafeWrite new i (unsafeCoerce @Word8 @Int $ s VU.! i)
  sais new 128

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