module Transform where

import Term
import Context
import LTS
import Exception
import Data.List
import Data.Maybe (isJust)
import Debug.Trace

drive t m = drive' t EmptyCtx (free t) m []
drive' (Free x) k fv m d = driveCtx (Node (Free x) []) k fv m d
drive' (Bound i) k fv m d = error ("Unexpected bound variable")
drive' t@(Lambda x t') EmptyCtx fv m d = let x' = rename fv x
                                             l = drive' (subst (Free x') t') EmptyCtx (x':fv) m d
                                         in  Node t [abstractLTS x' l]
drive' (Lambda x t) (ApplyCtx k t') fv m d = drive' (subst t' t) k fv m d
drive' (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
drive' t@(Con c ts) EmptyCtx fv m d = Node t (map (\t -> drive' t EmptyCtx fv m d) ts)
drive' (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (Con c ts))
drive' t@(Con c ts) k@(CaseCtx k' bs) fv m d = case (find (\(c',xs,t) -> c==c' && length xs == length ts) bs) of
                                                  Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                  Just (c',xs,t) -> let u = place t k
                                                                    in  ConElim c u (drive' (foldr (\t t' -> subst t t') t ts) k' fv m d)
drive' (Apply t u) k fv m d = drive' t (ApplyCtx k u) fv m d
drive' (Fun f) k fv m d = let t = place (Fun f) k
                          in case (find (\(f',t') -> isJust (embed t' t)) m) of
                                Just (f',_) -> case (lookup f d) of
                                                  Nothing -> error ("Undefined function: "++f)
                                                  Just t' -> let l = Unfold f t (drive' t' k fv [("f",t)] d)
                                                             in  Embedding f' (if "f" `elem` (embeddings [] l) then Function "f" l else l)
                                Nothing -> case (lookup f d) of
                                              Nothing -> error ("Undefined function: "++f)
                                              Just t' -> let f' = rename (fst (unzip m)) "f"
                                                             l = Unfold f t (drive' t' k fv ((f',t):m) d)
                                                         in if  f' `elem` (embeddings [] l) then Function f' l else l
drive' (Case t bs) k fv m d = drive' t (CaseCtx k bs) fv m d
drive' t@(Let x t' u) k fv m d = let x' = rename fv x
                                     l = drive' t' EmptyCtx fv m d
                                     l' = drive' (subst (Free x') u) k (x':fv) m d
                                 in  Node t [l,abstractLTS x' l']
drive' (Where t ds) k fv m d = drive' t k fv m (ds++d)

driveCtx l EmptyCtx fv m d = l
driveCtx l (ApplyCtx k t) fv m d = let l' = drive' t EmptyCtx fv m d
                                   in  driveCtx (Node (Apply (root l) t) [l,l']) k fv m d
driveCtx l@(Node (Free x) []) (CaseCtx k bs) fv m d = Node (Case (Free x) bs) (l:map (\(c,xs,t) -> let t' = place t k
                                                                                                       fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                                                       xs' = take (length xs) fv'
                                                                                                       u = foldr (\x t -> subst (Free x) t) (subst (Con c (map Free xs')) (abstract x t')) xs'
                                                                                                       l' = drive' u EmptyCtx fv' m d
                                                                                                   in  foldl (\t x -> abstractLTS x t) l' xs') bs)
driveCtx l (CaseCtx k bs) fv m d = Node (Case (root l) bs) (l:map (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                                    xs' = take (length xs) fv'
                                                                                    u = foldr (\x t -> subst (Free x) t) t xs'
                                                                                    l' = drive' u k fv' m d
                                                                                in  foldl (\t x -> abstractLTS x t) l' xs') bs)

