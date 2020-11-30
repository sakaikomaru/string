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

type SuffixArray = VUM.IOVector Int

inducedSort :: SuffixArray -> VU.Vector Int -> VU.Vector Bool -> VU.Vector Int -> Int -> IO ()
inducedSort sa vec sl lmsIdx valRange = do
  l <- VUM.unsafeNew valRange :: IO (VUM.IOVector Int)
  r <- VUM.unsafeNew valRange :: IO (VUM.IOVector Int)
  VU.forM_ vec $ \c -> do
    when (c + 1 < valRange) $ VUM.unsafeModify l succ (c + 1)
    VUM.unsafeModify r succ c
  rep1 valRange $ \i -> do
    item <- VUM.unsafeRead l (i - 1)
    VUM.unsafeModify l (+ item) i
  rep1 valRange $ \i -> do
    item <- VUM.unsafeRead r (i - 1)
    VUM.unsafeModify r (+ item) i
  rep (VUM.length sa) $ \i -> VUM.unsafeWrite sa i (-1)
  rev (VU.length lmsIdx) $ \i -> do
    let _idx = vec VU.! (lmsIdx VU.! i)
    VUM.unsafeModify r pred _idx
    item <- VUM.unsafeRead r _idx
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

createLMSIdx :: VU.Vector Int -> Int -> IO (VU.Vector Int, VU.Vector Bool)
createLMSIdx vec n = do
  lmsIdx <- VUM.unsafeNew n :: IO (VUM.IOVector Int)
  sl     <- VUM.unsafeNew n :: IO (VUM.IOVector Bool)
  VUM.unsafeWrite sl (n - 1) False
  rangeR (n - 2) 0 $ \i -> do
    let
      veci  = vec VU.! i
      veci1 = vec VU.! (i + 1)
    sli1 <- VUM.unsafeRead sl (i + 1)
    let
      check = veci > veci1 || (veci == veci1 && sli1)
    VUM.unsafeWrite sl i check
    when (check && not sli1) $ VUM.unsafeWrite lmsIdx ((n - 2) - i) (i + 1)
  target1 <- VU.reverse . VU.filter (/= 0) <$> VU.unsafeFreeze lmsIdx
  target2 <- VU.unsafeFreeze sl
  return (target1, target2)

createLMSVec :: SuffixArray -> VU.Vector Int -> Int -> VU.Vector Int -> Int -> VU.Vector Bool -> IO (VUM.IOVector Int, VU.Vector Int, Int)
createLMSVec sa vec n lmsIdx lmSize sl = do
  newLMSIdx <- VUM.unsafeNew lmSize :: IO (VUM.IOVector Int)
  lmsVec    <- VUM.unsafeNew lmSize :: IO (VUM.IOVector Int)
  kRef <- newIORef (0 :: Int)
  rep n $ \i -> do
    sai <- VUM.unsafeRead sa i
    let
      check1 = not $ sl VU.! sai
      check2 = sai >= 1
      check3 = sl VU.! (sai - 1)
    when (check1 && check2 && check3) $ do
      k <- readIORef kRef
      VUM.unsafeWrite newLMSIdx k sai
      modifyIORef kRef succ
  curRef <- newIORef (0 :: Int)
  VUM.unsafeWrite sa (n - 1) 0
  rep1 lmSize $ \k -> do
    i <- VUM.unsafeRead newLMSIdx (k - 1)
    j <- VUM.unsafeRead newLMSIdx k
    if vec VU.! i /= vec VU.! j
      then do
        modifyIORef' curRef succ
        VUM.unsafeWrite sa j =<< readIORef curRef
      else do
        flagRef <- newIORef False
        aRef    <- newIORef (i + 1)
        bRef    <- newIORef (j + 1)
        withBreakIO $ \break -> rep n $ \_ -> do
          a <- liftIO $ readIORef aRef
          b <- liftIO $ readIORef bRef
          when (vec VU.! a /= vec VU.! b) $ do
            liftIO $ writeIORef flagRef True
            break ()
          let
            check4 = not $ sl VU.! a  
            check5 = sl VU.! (a - 1)
            check6 = not $ sl VU.! b
            check7 = sl VU.! (b - 1)
            check8 = (check4 && check5) || (check6 && check7)
          when check8 $ do
            liftIO $ writeIORef flagRef (not check8)
            break()
        flag <- readIORef flagRef
        cur  <- readIORef curRef
        VUM.unsafeWrite sa j (bool cur (cur + 1) flag)
        when flag $ modifyIORef curRef succ
  rep lmSize $ \i -> do
    item <- VUM.unsafeRead sa (lmsIdx VU.! i)
    VUM.unsafeWrite lmsVec i item
  target1 <- VU.unsafeFreeze lmsVec
  target2 <- readIORef curRef
  return (newLMSIdx, target1, target2)

sais :: SuffixArray -> VU.Vector Int -> Int -> IO ()
sais sa vec valRange = do
  let n = VU.length vec
  (lmsIdx, sl) <- createLMSIdx vec n
  inducedSort sa vec sl lmsIdx valRange
  let lmSize = VU.length lmsIdx
  (newlmsIdx, lmsVec, cur) <- createLMSVec sa vec n lmsIdx lmSize sl
  when (cur + 1 < lmSize) $ do
    sa' <- VUM.unsafeNew (VU.length lmsVec + 1) :: IO SuffixArray
    sais sa' lmsVec (cur + 1)
    rep (VU.length lmsVec) $ \i -> do
      item <- VUM.unsafeRead sa' i
      VUM.unsafeWrite newlmsIdx i (lmsIdx VU.! item)
  newLMSIDX <- VU.unsafeFreeze newlmsIdx
  inducedSort sa vec sl newLMSIDX valRange

suffixArray :: VU.Vector Word8 -> IO (VU.Vector Int)
suffixArray vec = do
  sa <- VUM.unsafeNew (1 + VU.length vec) :: IO (VUM.IOVector Int)
  let vec' = (VU.++ VU.singleton 36) $ VU.map (unsafeCoerce @Word8 @Int) vec
  sais sa vec' 128
  VU.tail <$> VU.unsafeFreeze sa


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
