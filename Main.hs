{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import           Control.Monad
import           Control.Monad.Cont
import           Control.Monad.Fix
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Bool
import           Data.Char
import           Data.Coerce
import           Data.Int
import           Data.IORef
import           Data.Maybe
import           Data.STRef
import           Data.Word
import           System.IO
import           Unsafe.Coerce
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Builder           as BSB
import qualified Data.ByteString.Char8             as BSC8
import qualified Data.Vector.Fusion.Stream.Monadic as VFSM
import qualified Data.Vector.Generic               as VG
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

main :: IO ()
main = do
  xs <- BSC8.getLine
  let n = BSC8.length xs
  printVecInSpcSepLn . VU.tail . suffixArray . VU.unfoldrN n (runCParser byte) $ xs

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

type CParser a = StateT BSC8.ByteString Maybe a
runCParser :: CParser a -> BSC8.ByteString -> Maybe (a, BSC8.ByteString)
runCParser = runStateT
{-# INLINE runCParser #-}
int :: CParser Int
int = coerce $ BSC8.readInt . BSC8.dropWhile isSpace
{-# INLINE int #-}
int1 :: CParser Int
int1 = fmap (subtract 1) int
{-# INLINE int1 #-}
char :: CParser Char
char = coerce BSC8.uncons
{-# INLINE char #-}
byte :: CParser Word8
byte = coerce BS.uncons
{-# INLINE byte #-}
skipSpaces :: CParser ()
skipSpaces = modify' (BSC8.dropWhile isSpace)
{-# INLINE skipSpaces #-}
seqInput :: Int -> IO (VU.Vector Int)
seqInput n = VU.unfoldrN n (runCParser int) <$> BSC8.getLine
{-# INLINE seqInput #-}
parseN1 :: Int -> IO (VU.Vector Int)
parseN1 n = VU.unfoldrN n (runCParser int) <$> BSC8.getContents
{-# INLINE parseN1 #-}
parseN2 :: Int -> IO (VU.Vector (Int, Int))
parseN2 n = VU.unfoldrN n (runCParser $ (,) <$> int <*> int) <$> BSC8.getContents
{-# INLINE parseN2 #-}
parseN3 :: Int -> IO (VU.Vector (Int, Int, Int))
parseN3 n = VU.unfoldrN n (runCParser $ (,,) <$> int <*> int <*> int) <$> BSC8.getContents
{-# INLINE parseN3 #-}
parseN4 :: Int -> IO (VU.Vector (Int, Int, Int, Int))
parseN4 n = VU.unfoldrN n (runCParser $ (,,,) <$> int <*> int <*> int <*> int) <$> BSC8.getContents
{-# INLINE parseN4 #-}
parseN5 :: Int -> IO (VU.Vector (Int, Int, Int, Int, Int))
parseN5 n = VU.unfoldrN n (runCParser $ (,,,,) <$> int <*> int <*> int <*> int <*> int) <$> BSC8.getContents
{-# INLINE parseN5 #-}
parseANBN :: Int -> IO (VU.Vector Int, VU.Vector Int)
parseANBN n = VU.unzip . VU.unfoldrN n (runCParser $ (,) <$> int <*> int) <$> BSC8.getContents
{-# INLINE parseANBN #-}
parseANBNCN :: Int -> IO (VU.Vector Int, VU.Vector Int, VU.Vector Int)
parseANBNCN n = VU.unzip3 . VU.unfoldrN n (runCParser $ (,,) <$> int <*> int <*> int) <$> BSC8.getContents
{-# INLINE parseANBNCN #-}

type Query3 = (Int, Int, Int)
query3Parser :: CParser Query3
query3Parser = do
  skipSpaces
  t <- char
  case t of
    '0' -> (,,) 0 <$> int <*> int
    _   -> (,,) 1 <$> int <*> pure 0
parseQ3 :: Int -> IO (VU.Vector Query3)
parseQ3 n = VU.unfoldrN n (runCParser query3Parser) <$> BSC8.getContents
{-# INLINE parseQ3 #-}

type Query5 = (Int, Int, Int, Int, Int)
query5Parser :: CParser Query5
query5Parser = do
  skipSpaces
  t <- char
  case t of
    '0' -> (,,,,) 0 <$> int <*> int <*> int    <*> int
    _   -> (,,,,) 1 <$> int <*> int <*> pure 0 <*> pure 0
parseQ5 :: Int -> IO (VU.Vector Query5)
parseQ5 n = VU.unfoldrN n (runCParser query5Parser) <$> BSC8.getContents
{-# INLINE parseQ5 #-}

readInt :: BSC8.ByteString -> Int
readInt = fst . fromJust . BSC8.readInt
{-# INLINE readInt #-}
getInt :: IO Int
getInt = readInt <$> BSC8.getLine
{-# INLINE getInt #-}
readIntList :: BSC8.ByteString -> [Int]
readIntList = map readInt . BSC8.words
{-# INLINE readIntList #-}
getIntList :: IO [Int]
getIntList = readIntList <$> BSC8.getLine
{-# INLINE getIntList #-}
readInteger :: BSC8.ByteString -> Integer
readInteger = fst . fromJust . BSC8.readInteger
{-# INLINE readInteger #-}
getInteger :: IO Integer
getInteger = readInteger <$> BSC8.getLine
{-# INLINE getInteger #-}
readIntegerList :: BSC8.ByteString -> [Integer]
readIntegerList = map readInteger . BSC8.words
{-# INLINE readIntegerList #-}
getIntegerList :: IO [Integer]
getIntegerList = readIntegerList <$> BSC8.getLine
{-# INLINE getIntegerList #-}

class ShowAsBuilder a where
  showAsBuilder :: a -> BSB.Builder
  default showAsBuilder :: (Show a) => a -> BSB.Builder
  showAsBuilder = BSB.string8 . show

instance ShowAsBuilder Int where
  showAsBuilder = BSB.intDec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Int8 where
  showAsBuilder = BSB.int8Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Int16 where
  showAsBuilder = BSB.int16Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Int32 where
  showAsBuilder = BSB.int32Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Int64 where
  showAsBuilder = BSB.int64Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Word8 where
  showAsBuilder = BSB.word8Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Word16 where
  showAsBuilder = BSB.word16Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Word32 where
  showAsBuilder = BSB.word32Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Word64 where
  showAsBuilder = BSB.word64Dec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Integer where
  showAsBuilder = BSB.integerDec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Float where
  showAsBuilder = BSB.floatDec
  {-# INLINE showAsBuilder #-}
instance ShowAsBuilder Double where
  showAsBuilder = BSB.doubleDec
  {-# INLINE showAsBuilder #-}

instance (ShowAsBuilder a, VG.Vector v a) => ShowAsBuilder (v a) where
  showAsBuilder = v2BSpcSep

putBuilder :: BSB.Builder -> IO ()
putBuilder = BSB.hPutBuilder stdout
{-# INLINE putBuilder #-}

printVecInLines :: (VG.Vector v a, ShowAsBuilder a) => v a -> IO ()
printVecInLines = putBuilder . v2BLines
{-# INLINE printVecInLines #-}

printVecInSpcSepLn :: (VG.Vector v a, ShowAsBuilder a) => v a -> IO ()
printVecInSpcSepLn = putBuilder . v2BSpcSepLn
{-# INLINE printVecInSpcSepLn #-}

v2BSpcSepLn :: (VG.Vector v a, ShowAsBuilder a) => v a -> BSB.Builder
v2BSpcSepLn = v2BSpcSepLnWith showAsBuilder
{-# INLINE v2BSpcSepLn #-}

v2BSpcSep :: (VG.Vector v a, ShowAsBuilder a) => v a -> BSB.Builder
v2BSpcSep = v2BSpcSepWith showAsBuilder
{-# INLINE v2BSpcSep #-}

v2BConcat:: (VG.Vector v a, ShowAsBuilder a) => v a -> BSB.Builder
v2BConcat = v2BConcatWith showAsBuilder
{-# INLINE v2BConcat #-}

v2BLines:: (VG.Vector v a, ShowAsBuilder a) => v a -> BSB.Builder
v2BLines = v2BLinesWith showAsBuilder
{-# INLINE v2BLines #-}

v2BSpcSepLnWith :: VG.Vector v a => (a -> BSB.Builder) -> v a -> BSB.Builder
v2BSpcSepLnWith = v2BSpcSepPostfWith "\n"
{-# INLINE v2BSpcSepLnWith #-}

v2BSpcSepWith :: VG.Vector v a => (a -> BSB.Builder) -> v a -> BSB.Builder
v2BSpcSepWith = v2BSpcSepPostfWith ""
{-# INLINE v2BSpcSepWith #-}

v2BConcatWith :: VG.Vector v a => (a -> BSB.Builder) -> v a -> BSB.Builder
v2BConcatWith showFct = VG.foldr ((<>) . showFct) mempty
{-# INLINE v2BConcatWith #-}

v2BLinesWith :: VG.Vector v a => (a -> BSB.Builder) -> v a -> BSB.Builder
v2BLinesWith showFct = VG.foldr (\a -> (showFct a <>) . (BSB.char7 '\n' <>)) mempty
{-# INLINE v2BLinesWith #-}

v2BSpcSepPostf :: (VG.Vector v a, ShowAsBuilder a) => BS.ByteString -> v a -> BSB.Builder
v2BSpcSepPostf = (`v2BSpcSepPostfWith` showAsBuilder)
{-# INLINE v2BSpcSepPostf #-}

v2BSpcSepPostfWith :: VG.Vector v a => BS.ByteString -> (a -> BSB.Builder) -> v a -> BSB.Builder
v2BSpcSepPostfWith = vecToBuilder "" " "
{-# INLINE v2BSpcSepPostfWith #-}

vecToBuilder :: VG.Vector v a => BS.ByteString -> BS.ByteString -> BS.ByteString -> (a -> BSB.Builder) -> v a -> BSB.Builder
vecToBuilder !prefix !separator !postfix = vecToBuilder_ (BSB.byteString prefix) (BSB.byteString separator) (BSB.byteString postfix)
{-# INLINE vecToBuilder #-}

vecToBuilder_ :: VG.Vector v a => BSB.Builder -> BSB.Builder -> BSB.Builder -> (a -> BSB.Builder) -> v a -> BSB.Builder
vecToBuilder_ !prefix !separator !postfix showFct vec = prefix <> VG.foldr (\a rest !prefx -> prefx <> (showFct a <> rest separator)) (const postfix) vec mempty
{-# INLINE vecToBuilder_ #-}