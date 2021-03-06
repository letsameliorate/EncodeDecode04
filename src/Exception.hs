-----------------------------------------------------------------------------
--
-- Module      :  Exception
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Exception where

data Exception a b = Exn a | NoExn b deriving Show

instance Monad (Exception a) where
    return x = NoExn x
    (>>=) (Exn d) f = (Exn d)
    (>>=) (NoExn a) f = f a

handle :: Exception a b -> (a -> Exception a b) -> Exception a b
handle x f = case x of
               Exn c -> f c
               NoExn a -> NoExn a

throw :: a -> Exception a b
throw x = Exn x

returnval (NoExn a) = a