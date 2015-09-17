-----------------------------------------------------------------------------
--
-- Module      :  Eval
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

module Eval where

import Term
import Data.List
import Debug.Trace

evalnf (Free x) env r a = error ("Unbound identifier: "++x)
evalnf (Binop b t u) env r a = let (t',r',a') = evalnf t env r a
                                   (u',r'',a'') = evalnf u env r' a'
                                   v1 = con2nat t'
                                   v2 = con2nat u'
                               in  case b of
                                      "+" -> (nat2con (v1 + v2),r''+1,a'')
                                      "-" -> if   v2 > v1
                                             then error ("Negative value for natural number: " ++ show (Binop b t u))
                                             else (nat2con (v1 - v2),r''+1,a'')
                                      "*" -> (nat2con (v1 * v2),r''+1,a'')
                                      "/" -> (nat2con (v1 `div` v2),r''+1,a'')
evalnf (Lambda x t) env r a = (Lambda x t,r,a)
evalnf t@(Con c ts) env r a = let (ts',r',a') = foldr (\t (ts,r,a) -> let (t',r',a') = evalnf t env r a
                                                                      in  (t':ts,r',a')) ([],r,a) ts
                              in  (Con c ts',r'+1,a'+1)
evalnf (Apply t u) env r a = case (evalwhnf t env r a) of
                                (Lambda x t',r',a') -> evalnf (subst u t') env (r'+1) a'
                                _ -> error ("Non-function in application: " ++ show t)
evalnf (Fun f) env r a = case lookup f env of
                            Nothing -> error ("Undefined function: "++f)
                            Just t  -> evalnf t env (r+1) a
evalnf (Case t bs) env r a = case (evalwhnf t env r a) of
                                (Con c ts,r',a') -> case (find (\(c',xs,u) -> c==c' && length xs == length ts) bs) of
                                                       Nothing -> error ("No matching pattern in case: " ++ show (Case t bs))
                                                       Just (c',xs,u) -> evalnf (foldr (\t u -> subst t u) u ts) env (r'+length ts) a'
                                u -> error ("Non-constructor in case selector: " ++ show t)
evalnf (Let x t u) env r a = evalnf (subst t u) env (r+1) a
evalnf (Where t ds) env r a = evalnf t (ds++env) (r+1) a

evalwhnf (Free x) env r a = error ("Unbound identifier: "++x)
evalwhnf (Lambda x t) env r a = (Lambda x t,r,a)
evalwhnf (Con c ts) env r a = (Con c ts,r+1,a+1)
evalwhnf (Apply t u) env r a = case (evalwhnf t env r a) of
                                  (Lambda x t',r',a') -> evalwhnf (subst u t') env (r'+1) a'
                                  _ -> error ("Non-function in application: " ++ show t)
evalwhnf (Fun f) env r a = case lookup f env of
                              Nothing -> error ("Undefined function: "++f)
                              Just t  -> evalwhnf t env (r+1) a
evalwhnf (Case t bs) env r a = case (evalwhnf t env r a) of
                                  (Con c ts,r',a') -> case (find (\(c',xs,u) -> c==c' && length xs == length ts) bs) of
                                                         Nothing -> error ("No matching pattern in case: " ++ show (Case t bs))
                                                         Just (c',xs,u) -> evalwhnf (foldr (\t u -> subst t u) u ts) env (r'+1) a'
                                  u -> error ("Non-constructor in case selector: " ++ show t)
evalwhnf (Let x t u) env r a = evalwhnf (subst t u) env (r+1) a
evalwhnf (Where t ds) env r a = evalwhnf t (ds++env) (r+1) a

