-----------------------------------------------------------------------------
--
-- Module      :  Transform
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

module Transform where

import Term
--import LTS
import Exception
import Data.List
import Data.Maybe (isJust,isNothing)
import Debug.Trace

super t k fv m d = super' t k fv m d
super' (Free x) (CaseCtx k bs) fv m d = do
                                        bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                      fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                      xs' = take (length xs) fv'
                                                                      u = subst (Con c (map Free xs')) (abstract x (foldr (\x t -> subst (Free x) t) t' xs'))
                                                                  in do
                                                                     u' <- super u EmptyCtx fv' m d
                                                                     return (c,xs,foldl (\t x -> abstract x t) u' xs')) bs
                                        return (Case (Free x) bs')
super' (Free x) k fv m d = superCtx (Free x) k fv m d
super' (Binop b t u) k fv m d = super t (Leftop b k u) fv m d
super' (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                      in do
                                         t' <- super (subst (Free x') t) EmptyCtx (x':fv) m d
                                         return (Lambda x (abstract x' t'))
super' (Lambda x t) (ApplyCtx k (Lambda x' t')) fv m d = let f = rename (fst (unzip d)) "f"
                                                         in  super (subst (Fun f) t) k fv m ((f,Lambda x' t'):d)
super' (Lambda x t) (ApplyCtx k u) fv m d = super (subst u t) k fv m d
super' (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
super' (Lambda x t) (Leftop b k u) fv m d = error "Unapplied function in basic function argument"
super' (Con c ts) EmptyCtx fv m d = do
                                    ts' <- mapM (\t -> super t EmptyCtx fv m d) ts
                                    return (Con c ts')
super' (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) k))
super' (Con c ts) (CaseCtx k bs) fv m d = case (find (\(c',xs,t) -> c==c' && length xs == length ts) bs) of
                                             Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                             Just (c',xs,t) -> super (foldr (\t t' -> subst t t') t ts) k fv m d
super' (Con c ts) (Leftop b k t) fv m d = error "Constructor in basic function argument"
super' (Apply t u) k fv m d = super t (ApplyCtx k u) fv m d
super' (Fun f) k fv m d = let t = place (Fun f) k
                          in  case (find (\(Node n ts t') -> isJust (inst t' t)) m) of
                                 Just (Node n ts t') -> let Just s = inst t' t
                                                        in  return (instantiate s (Repeat n ts))
                                 Nothing -> case (find (\(Node n ts t') -> isJust (embed t' t)) m) of
                                               Just (Node n ts t') -> throw (n,t)
                                               Nothing -> let (t',d') = unfold t d
                                                              n = rename fv "f"
                                                              xs = free t
                                                              handler = \(n',t') -> if   n==n'
                                                                                    then let (t'',s) = generalise t t'
                                                                                         in  super (makeLet s t'') EmptyCtx fv m d
                                                                                    else throw (n',t')
                                                              u = do
                                                                  u' <- super t' EmptyCtx (n:fv) ((Node n (map Free xs) t):m) d'
                                                                  return (if n `elem` repeats u' then (Node n (map Free xs) u') else u')
                                                          in handle u handler
super' (Case t bs) k fv m d = super t (CaseCtx k bs) fv m d
super' (Let x t u) k fv m d = let x' = rename fv x
                              in do
                                 t' <- super t EmptyCtx fv m d
                                 u' <- super (subst (Free x') u) k (x':fv) m d
                                 return (Let x t' (abstract x' u'))
super' (Where t ds) k fv m d = super t k fv m (ds++d)

superCtx t EmptyCtx fv m d = return t
superCtx t (ApplyCtx k u) fv m d = do
                                   u' <- super u EmptyCtx fv m d
                                   superCtx (Apply t u') k fv m d
superCtx t (CaseCtx k bs) fv m d = do
                                   bs' <- mapM (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                 xs' = take (length xs) fv'
                                                             in do
                                                                t' <- super (foldr (\x t -> subst (Free x) t) t xs') k fv' m d
                                                                return (c,xs,foldl (\t x -> abstract x t) t' xs')) bs
                                   return (Case t bs')
superCtx t (Leftop b k u) fv m d = do
                                   u' <- super u EmptyCtx fv m d
                                   superCtx (Binop b t u') k fv m d

distill t k fv m d = distill' t k fv m d
distill' (Free x) (CaseCtx k bs) fv m d = do
                                          bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                        fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                        xs' = take (length xs) fv'
                                                                        u = subst (Con c (map Free xs')) (abstract x (foldr (\x t -> subst (Free x) t) t' xs'))
                                                                    in do
                                                                       u' <- distill u EmptyCtx fv' m d
                                                                       return (c,xs,foldl (\t x -> abstract x t) u' xs')) bs
                                          return (Case (Free x) bs')
distill' (Free x) k fv m d = distillCtx (Free x) k fv m d
distill' (Binop b t u) k fv m d = distill t (Leftop b k u) fv m d
distill' (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                        in do
                                           t' <- distill (subst (Free x') t) EmptyCtx (x':fv) m d
                                           return (Lambda x (abstract x' t'))
distill' (Lambda x t) (ApplyCtx k (Lambda x' t')) fv m d = let f = rename (fst (unzip d)) "f"
                                                           in  distill (subst (Fun f) t) k fv m ((f,Lambda x' t'):d)
distill' (Lambda x t) (ApplyCtx k u) fv m d = distill (subst u t) k fv m d
distill' (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
distill' (Lambda x t) (Leftop b k u) fv m d = error "Unapplied function in basic function argument"
distill' (Con c ts) EmptyCtx fv m d = do
                                      ts' <- mapM (\t -> distill t EmptyCtx fv m d) ts
                                      return (Con c ts')
distill' (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) k))
distill' (Con c ts) (CaseCtx k bs) fv m d = case (find (\(c',xs,t) -> c==c' && length xs == length ts) bs) of
                                               Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                               Just (c',xs,t) -> distill (foldr (\t t' -> subst t t') t ts) k fv m d
distill' (Con c ts) (Leftop b k t) fv m d = error "Constructor in basic function argument"
distill' (Apply t u) k fv m d = distill t (ApplyCtx k u) fv m d
distill' (Fun f) k fv m d = let t = returnval (super (Fun f) k fv [] d)
                            in  trace (show t) (case (find (\(Node n ts t') -> isJust (inst t' t)) m) of
                                   Just (Node n ts t') -> let Just s = inst t' t
                                                          in  return (makeLet s (Repeat n ts))
                                   Nothing -> case (find (\(Node n ts t') -> isJust (embed t' t)) m) of
                                                 Just (Node n ts t') -> throw (n,t)
                                                 Nothing -> let (t',d') = unfold (residualize t) []
                                                                n = rename fv "f"
                                                                xs = free t
                                                                handler = \(n',t') -> if   n==n'
                                                                                      then let (u,s) = generalise t t'
                                                                                               s' = map (\(x,t) -> (x,residualize t)) s
                                                                                               u' = residualize u
                                                                                           in  distill (makeLet s' u') EmptyCtx fv m d
                                                                                      else throw (n',t')
                                                                u = do
                                                                    u' <- distill t' EmptyCtx (n:fv) ((Node n (map Free xs) t):m) d'
                                                                    return (if n `elem` repeats u' then Node n (map Free xs) u' else u')
                                                            in handle u handler)
distill' (Case t bs) k fv m d = distill t (CaseCtx k bs) fv m d
distill' (Let x t u) k fv m d = let x' = rename fv x
                                in do
                                   t' <- distill t EmptyCtx fv m d
                                   u' <- distill (subst (Free x') u) k (x':fv) m d
                                   return (Let x t' (abstract x' u'))
distill' (Where t ds) k fv m d = distill t k fv m (ds++d)

distillCtx t EmptyCtx fv m d = return t
distillCtx t (ApplyCtx k u) fv m d = do
                                     u' <- distill u EmptyCtx fv m d
                                     distillCtx (Apply t u') k fv m d
distillCtx t (CaseCtx k bs) fv m d = do
                                     bs' <- mapM (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                   xs' = take (length xs) fv'
                                                               in do
                                                                  t' <- distill (foldr (\x t -> subst (Free x) t) t xs') k fv' m d
                                                                  return (c,xs,foldl (\t x -> abstract x t) t' xs')) bs
                                     return (Case t bs')
distillCtx t (Leftop b k u) fv m d = do
                                     u' <- distill u EmptyCtx fv m d
                                     distillCtx (Binop b t u') k fv m d