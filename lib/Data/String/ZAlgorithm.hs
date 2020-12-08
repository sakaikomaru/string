{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Monad.State
import           Data.Char
import           Data.Coerce
import           Data.Int
import           Data.Maybe
import           Data.Word
import           System.IO
import qualified Data.ByteString                   as BS
import qualified Data.ByteString.Builder           as BSB
import qualified Data.ByteString.Char8             as BSC8
import qualified Data.ByteString.Unsafe            as BSU
import qualified Data.Vector.Generic               as VG
import qualified Data.Vector.Unboxed               as VU
import qualified Data.Vector.Unboxed.Mutable       as VUM

main :: IO ()
main = BSC8.getLine >>= printVecInSpcSepLn . zAlgorithm

zAlgorithm :: BSC8.ByteString -> VU.Vector Int
zAlgorithm bs
  | n == 0    = VU.empty
  | otherwise = VU.create $ do
    z <- VUM.replicate n 0
    vl <- VUM.replicate 1 0
    vr <- VUM.replicate 1 0
    VU.forM_ (VU.generate n (+1)) $ \i -> do
      r <- VUM.unsafeRead vr 0
      if i > r
      then do
        let r' = searchR i i
        VUM.unsafeWrite z i (r' - i)
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
