module Main where

import Term
import Context
import LTS
import Exception
import Transform

main :: IO ()
main = do
          putStrLn ""
          let Right e1Term = parseProg "f xs ys p where f = \\xs ys p. case xs of Nil -> Nil | Cons(x,xs) -> case ys of Nil -> Nil | Cons(y,ys) -> Cons((p x y),f xs ys p)"
              e1LTS = drive e1Term
              Right e2Term = parseProg "g xs q where g = \\xs q. case xs of Nil -> Nil | Cons(x,xs) -> Cons(q x,g xs q)"
              e2LTS = drive e2Term

              Right mapTerm = parseProg "map ys p where map = \\ys p. case ys of Nil -> Nil | Cons(y,ys) -> Cons(p y,map ys p)"
              mapLTS = drive mapTerm
              Right foldrTerm = parseProg "foldr ys p v where foldr = \\ys p v. case ys of Nil -> v | Cons(y,ys) -> p y (foldr ys p v)"
              foldrLTS = drive foldrTerm
              Right zipWithTerm = parseProg "zipWith xs ys f where zipWith = \\xs ys f. case xs of Nil -> Nil | Cons(x,xs) -> case ys of Nil -> Nil | Cons(y,ys) -> Cons((f x y),(zipWith xs ys f))"
              zipWithLTS = drive zipWithTerm

          putStrLn ""
          print (instFuns mapLTS e2LTS)
          putStrLn ""
          print (instFuns foldrLTS e2LTS)