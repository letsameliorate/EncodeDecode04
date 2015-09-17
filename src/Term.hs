-----------------------------------------------------------------------------
--
-- Module      :  Term
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

module Term where

import Data.Char
import Data.Maybe
import Data.List (intersect,(\\))
import Data.Foldable (foldrM,find)
import Control.Monad
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language
import Debug.Trace

data Term = Free String
          | Bound Int
          | Binop String Term Term
          | Lambda String Term
          | Con String [Term]
          | Apply Term Term
          | Fun String
          | Case Term [(String,[String],Term)]
          | Let String Term Term
          | Where Term [(String,Term)]
          | Node String [Term] Term
          | Repeat String [Term]

instance Show Term where
   show t = render (prettyTerm t)

instance Eq Term where
   (==) l l' = eqTerm [] l l'

eqTerm ns (Free x) (Free x') = x==x'
eqTerm ns (Bound i) (Bound i') = i==i'
eqTerm ns (Binop b t u) (Binop b' t' u') | b==b' = (eqTerm ns t t') && (eqTerm ns u u')
eqTerm ns (Lambda x t) (Lambda x' t') = eqTerm ns t t'
eqTerm ns (Con c ts) (Con c' ts') | c==c' = all (\ (t,t') -> eqTerm ns t t') (zip ts ts')
eqTerm ns (Apply t u) (Apply t' u') = (eqTerm ns t t') && (eqTerm ns u u')
eqTerm ns (Fun f) (Fun f') = f==f'
eqTerm ns u@(Case t bs) u'@(Case t' bs') | match u u' = (eqTerm ns t t') && (all (\ ((c,xs,t),(c',xs',t')) -> eqTerm ns t t') (zip bs bs'))
eqTerm ns (Let x t u) (Let x' t' u') = (eqTerm ns t t') && (eqTerm ns u u')
eqTerm ns u@(Where t ds) u'@(Where t' ds') | match u u' = eqTerm ns t t'
eqTerm ns (Node n ts t) (Node n' ts' t') = eqTerm ((n,n'):ns) t t'
eqTerm ns (Repeat n ts) (Repeat n' ts') = (n,n') `elem` ns
eqTerm ns t t' = False

data Context = EmptyCtx
             | Leftop String Context Term
             | Rightop String Term Context
             | ApplyCtx Context Term
             | CaseCtx Context [(String,[String],Term)] deriving Show

place t EmptyCtx = t
place t (Leftop b con u) = place (Binop b t u) con
place t (Rightop b u con) = place (Binop b u t) con
place t (ApplyCtx con u) = place (Apply t u) con
place t (CaseCtx con bs) = place (Case t bs) con

renaming t t' = renaming' [] t t' []

renaming' ns (Free x) (Free x') r = if x `elem` fst (unzip r)
                                    then if (x,x') `elem` r then Just r else Nothing
                                    else Just ((x,x'):r)
renaming' ns (Bound i) (Bound i') r | i==i' = Just r
renaming' ns (Binop b t u) (Binop b' t' u') r | b==b' = (renaming' ns t t' r) >>= (renaming' ns u u')
renaming' ns (Lambda _ t) (Lambda _ t') r = renaming' ns t t' r
renaming' ns (Con c ts) (Con c' ts') r | c==c' = foldrM (\(t,t') r -> renaming' ns t t' r) r (zip ts ts')
renaming' ns (Apply t u) (Apply t' u') r = (renaming' ns t t' r) >>= (renaming' ns u u')
renaming' ns (Fun f) (Fun f') r | f==f' = Just r
renaming' ns u@(Case t bs) u'@(Case t' bs') r | match u u' = (renaming' ns t t' r) >>= (\r -> foldrM (\((_,_,t),(_,_,t')) r -> renaming' ns t t' r) r (zip bs bs'))
renaming' ns (Let _ t u) (Let _ t' u') r = (renaming' ns t t' r) >>= (renaming' ns u u')
renaming' ns u@(Where t ds) u'@(Where t' ds') r | match u u' = renaming' ns t t' r
renaming' ns (Node n ts t) (Node n' ts' t') r = renaming' ((n,n'):ns) t t' r
renaming' ns (Repeat n ts) (Repeat n' ts') r | (n,n') `elem` ns = Just r
renaming' ns t t' r = Nothing

inst t t' = inst' [] t t' []

inst' ns (Free x) t s = if x `elem` fst (unzip s)
                        then if (x,t) `elem` s then Just s else Nothing
                        else Just ((x,t):s)
inst' ns (Bound i) (Bound i') s | i==i' = Just s
inst' ns (Binop b t u) (Binop b' t' u') s | b==b' = (inst' ns t t' s) >>= (inst' ns u u')
inst' ns (Lambda _ t) (Lambda _ t') s = inst' ns t t' s
inst' ns (Con c ts) (Con c' ts') s | c==c' = foldrM (\(t,t') s -> inst' ns t t' s) s (zip ts ts')
inst' ns (Apply t u) (Apply t' u') s = (inst' ns t t' s) >>= (inst' ns u u')
inst' ns (Apply t u) t' s = msum (map (\u' -> (inst' ns u u' s) >>= (inst' ns t (Lambda "x" (abstractTerm 0 u' t')))) (subterms t'))
inst' ns (Fun f) (Fun f') s | f==f' = Just s
inst' ns u@(Case t bs) u'@(Case t' bs') s | match u u' = (inst' ns t t' s) >>= (\s -> foldrM (\((_,_,t),(_,_,t')) s -> inst' ns t t' s) s (zip bs bs'))
inst' ns (Let _ t u) (Let _ t' u') s = (inst' ns t t' s) >>= (inst' ns u u')
inst' ns u@(Where t ds) u'@(Where t' ds') s | match u u' = inst' ns t t' s
inst' ns (Node n ts t) (Node n' ts' t') s = inst' ((n,n'):ns) t t' s
inst' ns (Repeat n ts) (Repeat n' ts') s | (n,n') `elem` ns = Just s
inst' ns t t' s = Nothing

embed t u = couple [] t u []

embedding ns t u r = mplus (couple ns t u r) (dive ns t u r)

couple ns (Free x) (Free x') r = if x `elem` fst (unzip r)
                                 then if (x,x') `elem` r then Just r else Nothing
                                 else Just ((x,x'):r)
couple ns (Bound i) (Bound i') r | i == i' = Just r
couple ns (Binop b t u) (Binop b' t' u') r | b==b' = (embedding ns t t' r) >>= (embedding ns u u')
couple ns (Lambda _ t) (Lambda _' t') r = embedding ns t t' r
couple ns (Con c ts) (Con c' ts') r | c==c' = foldrM (\ (t,t') r -> embedding ns t t' r) r (zip ts ts')
couple ns (Apply t u) (Apply t' u') r = (embedding ns t t' r) >>= (embedding ns u u')
couple ns (Fun f) (Fun f') r | f==f' = Just r
couple ns u@(Case t bs) u'@(Case t' bs') r | match u u' = (embedding ns t t' r) >>= (\r->foldrM (\ ((_,_,t),(_,_,t')) r -> embedding ns t t' r) r (zip bs bs'))
couple ns (Let _ t u) (Let _ t' u') r = (embedding ns t t' r) >>= (embedding ns u u')
couple ns u@(Where t ds) u'@(Where t' ds') r | match u u' = couple ns t t' r
couple ns (Node n ts t) (Node n' ts' t') r = embedding ((n,n'):ns) t t' r
couple ns (Repeat n ts) (Repeat n' ts') r | (n,n') `elem` ns = Just r
couple ns t t' r = Nothing

dive ns t (Binop b t' u) r = mplus (embedding ns t t' r) (embedding ns t u r)
dive ns t (Lambda x t') r = embedding ns (shift 1 0 t) t' r
dive ns t (Con c ts) r = msum (map (\t' -> embedding ns t t' r) ts)
dive ns t (Apply t' u) r = mplus (embedding ns t t' r) (embedding ns t u r)
dive ns t (Case t' bs) r = mplus (embedding ns t t' r) (msum (map (\(_,xs,t') -> embedding ns (shift (length xs) 0 t) t' r) bs))
dive ns t (Let x t' u) r = mplus (embedding ns t t' r) (embedding ns (shift 1 0 t) u r)
dive ns t (Where t' ds') r = embedding ns t t' r
dive ns t (Node n ts t') r = embedding ns t t' r
dive ns t t' r = Nothing

generalise t t' = generalise' [] t t' (free t) [] [] []

generalise' ns (Free x) (Free x') fv bv ls s = (Free x,s)
generalise' ns (Bound i) (Bound i') fv bv ls s | i==i' = (Bound i,s)
generalise' ns (Binop b t u) (Binop b' t' u') fv bv ls s | b==b' = let (t'',s') = generalise' ns t t' fv bv ls s
                                                                       (u'',s'') = generalise' ns u u' fv bv ls s'
                                                                   in  (Binop b t'' u'',s'')
generalise' ns (Lambda x t) (Lambda x' t') fv bv ls s = let x'' = rename (fv++bv++fst(unzip s)) x
                                                            (t'',s') = generalise' ns (subst (Free x'') t) (subst (Free x'') t') fv (x'':bv) ls s
                                                        in  (Lambda x (abstract x'' t''),s')
generalise' ns u@(Con c ts) u'@(Con c' ts') fv bv ls s | match u u' = let (ts'',s') = foldr (\(t,t') (ts'',s) -> let (t'',s') = generalise' ns t t' fv bv ls s
                                                                                                                 in  (t'':ts'',s')) ([],s) (zip ts ts')
                                                                      in  (Con c ts'',s')
generalise' ns (Apply t u) (Apply t' u') fv bv ls s = let (t'',s') = generalise' ns t t' fv bv ls s
                                                          (u'',s'') = generalise' ns u u' fv bv ls s'
                                                      in  (Apply t'' u'',s'')
generalise' ns (Fun f) (Fun f') fv bv ls s | f==f' = (Fun f,s)
generalise' ns u@(Case t bs) u'@(Case t' bs') fv bv ls s | match u u' = let (t'',s') = generalise' ns t t' fv bv ls s
                                                                            (bs'',s'') = foldr (\ ((c,xs,t),(c',xs',t')) (bs'',s) -> let bv' = foldr (\x bv -> let x' = rename bv x in x':bv) (fv++bv++fst(unzip s)) xs
                                                                                                                                         xs'' = take (length xs) bv'
                                                                                                                                         (t'',s') = generalise' ns (foldr (\x t -> subst (Free x) t) t xs'') (foldr (\x t -> subst (Free x) t) t' xs'') fv (xs''++bv) ls s
                                                                                                                                     in  ((c,xs,foldl (\t x -> abstract x t) t'' xs''):bs'',s')) ([],s') (zip bs bs')
                                                                        in  (Case t'' bs'',s'')
generalise' ns (Let x t u) (Let x' t' u') fv bv ls s = let x'' = rename (fv++bv++fst(unzip s)) x
                                                           (t'',s') = generalise' ns t t' fv bv ls s
                                                           (u'',s'') = generalise' ns (subst (Free x'') u) (subst (Free x'') u') (x'':fv) bv ((x'',t''):ls) s'
                                                       in  (Let x t'' (abstract x'' u''),s'')
generalise' ns u@(Where t ds) u'@(Where t' ds') fv bv ls s | match u u' = let (t'',s') = generalise' ns t t' fv bv ls s
                                                                          in  (Where t'' ds,s')
generalise' ns (Node n ts t) (Node n' ts' t') fv bv ls s = let (t'',s') = generalise' ((n,n'):ns) t t' fv bv ls s
                                                           in  (Node n ts t'',s')
generalise' ns (Repeat n ts) (Repeat n' ts') fv bv ls s | (n,n') `elem` ns = (Repeat n ts,s)
generalise' ns t t' fv bv ls s = let xs = intersect bv (free t)
                                     t'' = instantiate ls (foldl (\t x -> Lambda x (abstract x t)) t xs)
                                     x = rename (fv++bv++fst(unzip s)) "x"
                                 in (foldr (\x t -> Apply t (Free x)) (Free x) xs,(x,t''):s)

makeLet s t = foldr (\(x,t) u -> Let x t (abstract x u)) t s

match (Free x) (Free x') = x==x'
match (Bound i) (Bound i') = i==i'
match (Binop b t u) (Binop b' t' u') = b==b'
match (Lambda x t) (Lambda x' t') = True
match (Con c ts) (Con c' ts') = c==c' && length ts == length ts'
match (Apply t u) (Apply t' u') = True
match (Fun f) (Fun f') = f==f'
match (Case t bs) (Case t' bs') = (length bs == length bs') && (all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs'))
match (Let x t u) (Let x' t' u') = True
match (Where t ds) (Where t' ds') = ds == ds'
match (Node n ts t) (Node n' ts' t') = True
match (Repeat n ts) (Repeat n' ts') = True
match t t' = False

subterms t = t:subterms' t

subterms' (Free x) = []
subterms' (Bound i) = []
subterms' (Binop b t u) = subterms t ++ subterms u
subterms' (Lambda x t) = subterms (shift (-1) 0 t)
subterms' (Con c ts) = concat (map subterms ts)
subterms' (Apply t u) = subterms t ++ subterms u
subterms' (Fun f) = []
subterms' (Case t bs) = subterms t ++ concat (map (\(c,xs,t) -> subterms (shift (-(length xs)) 0 t)) bs)
subterms' (Let x t u) = subterms t ++ subterms (shift (-1) 0 u)
subterms' (Where t ds) = subterms t ++ concat (map (\(f,t) -> subterms t) ds)
subterms' (Node n ts t) = subterms t ++ concat (map subterms ts)
subterms' (Repeat n ts) = concat (map subterms ts)

free t = free' [] t

free' xs (Free x) = if (x `elem` xs) then xs else x:xs
free' xs (Bound i) = xs
free' xs (Binop b t u) = free' (free' xs t) u
free' xs (Lambda x t) = free' xs t
free' xs (Con c ts) = foldr (\t xs -> free' xs t) xs ts
free' xs (Apply t u) = free' (free' xs t) u
free' xs (Fun f) = xs
free' xs (Case t bs) = foldr (\(c,xs,t) xs' -> free' xs' t) (free' xs t) bs
free' xs (Let x t u) = free' (free' xs t) u
free' xs (Where t ds) = foldr (\(x,t) xs -> free' xs t) (free' xs t) ds
free' xs (Node n ts t) = free' xs t
free' xs (Repeat n ts) = foldr (\t xs -> free' xs t) xs ts

repeats t = repeats' [] t
repeats' ns (Free x) = ns
repeats' ns (Bound i) = ns
repeats' ns (Binop b t u) = repeats' (repeats' ns t) u
repeats' ns (Lambda x t) = repeats' ns t
repeats' ns (Con c ts) = foldr (\t ns -> repeats' ns t) ns ts
repeats' ns (Apply t u) = repeats' (repeats' ns t) u
repeats' ns (Fun f) = ns
repeats' ns (Case t bs) = foldr (\(c,xs,t) ns -> repeats' ns t) (repeats' ns t) bs
repeats' ns (Let x t u) = repeats' (repeats' ns t) u
repeats' ns (Where t ds) = repeats' ns t
repeats' ns (Node n ts t) = repeats' ns t
repeats' ns (Repeat n ts) = n:ns

shift 0 d u = u
shift i d (Free x) = Free x
shift i d (Bound i') = if i' >= d then Bound (i'+i) else Bound i'
shift i d (Binop b t u) = Binop b (shift i d t) (shift i d u)
shift i d (Lambda x t) = Lambda x (shift i (d+1) t)
shift i d (Con c ts) = Con c (map (shift i d) ts)
shift i d (Apply t u) = Apply (shift i d t) (shift i d u)
shift i d (Fun f) = Fun f
shift i d (Case t bs) = Case (shift i d t) (map (\(c,xs,t) -> (c,xs,shift i (d+length xs) t)) bs)
shift i d (Let x t u) = Let x (shift i d t) (shift i (d+1) u)
shift i d (Where t ds) = Where (shift i d t) (map (\(x,t) -> (x,shift i d t)) ds)
shift i d (Node n ts t) = Node n (map (shift i d) ts) (shift i d t)
shift i d (Repeat n ts) = Repeat n (map (shift i d) ts)

subst t u = subst' 0 t u

subst' i t (Free x) = Free x
subst' i t (Bound i') = if   i'<i
                        then Bound i'
                        else if   i'==i
                             then shift i 0 t
                             else Bound (i'-1)
subst' i t (Binop b t' u) = Binop b (subst' i t t') (subst' i t u)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Apply t' u) = Apply (subst' i t t') (subst' i t u)
subst' i t (Fun f) = Fun f
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Where t' ds) = Where (subst' i t t') (map (\(x,u) -> (x,subst' i t u)) ds)
subst' i t (Node n ts t') = Node n (map (subst' i t) ts) (subst' i t t')
subst' i t (Repeat n ts) = Repeat n (map (subst' i t) ts)

substList ts t = foldr (\t u -> subst t u) t ts

instantiate s t = instantiate' 0 s t

instantiate' d s (Free x) = case (lookup x s) of
                               Just t  -> shift d 0 t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Apply t u) = Apply (instantiate' d s t) (instantiate' d s u)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Where t ds) = Where (instantiate' d s t) (map (\(x,t) -> (x,instantiate' d s t)) ds)
instantiate' d s (Node n ts t) = Node n (map (instantiate' d s) ts) (instantiate' d s t)
instantiate' d s (Repeat n ts) = Repeat n (map (instantiate' d s) ts)

abstract x t = abstract' 0 x t

abstract' i x (Free x') = if x==x' then Bound i else Free x'
abstract' i x (Bound i') = if i'>=i then Bound (i'+1) else Bound i'
abstract' i x (Binop b t u) = Binop b (abstract' i x t) (abstract' i x u)
abstract' i x (Lambda x' t) = Lambda x' (abstract' (i+1) x t)
abstract' i x (Con c ts) = Con c (map (abstract' i x) ts)
abstract' i x (Apply t u) = Apply (abstract' i x t) (abstract' i x u)
abstract' i x (Fun f) = Fun f
abstract' i x (Case t bs) = Case (abstract' i x t) (map (\(c,xs,t) -> (c,xs,abstract' (i + length xs) x t)) bs)
abstract' i x (Let x' t u) = Let x' (abstract' i x t) (abstract' (i+1) x u)
abstract' i x (Where t ds) = Where (abstract' i x t) (map (\(x',t) -> (x',abstract' i x t)) ds)
abstract' i x (Node n ts t) = Node n (map (abstract' i x) ts) (abstract' i x t)
abstract' i x (Repeat n ts) = Repeat n (map (abstract' i x) ts)

abstractList xs t = foldl (\t x -> abstract x t) t xs

abstractTerm i t u = if t==u then Bound i else abstractTerm' i t u
abstractTerm' i t (Free x) = Free x
abstractTerm' i t (Bound i') = Bound (if i'>=i then i'+1 else i')
abstractTerm' i t (Binop b t' u) = Binop b (abstractTerm i t t') (abstractTerm i t u)
abstractTerm' i t (Lambda x t') = Lambda x (abstractTerm (i+1) (shift 1 0 t) t')
abstractTerm' i t (Con c ts) = Con c (map (abstractTerm i t) ts)
abstractTerm' i t (Case t' bs) = Case (abstractTerm i t t') (map (\(c,xs,t') -> (c,xs,abstractTerm (i + length xs) (shift (length xs) 0 t) t')) bs)
abstractTerm' i t (Let x t' u) = Let x (abstractTerm i t t') (abstractTerm (i+1) (shift 1 0 t) u)
abstractTerm' i t (Where t' ds) = Where (abstractTerm i t t') (map (\(f,t') -> (f,abstractTerm i t t')) ds)
abstractTerm' i t (Node n ts t') = Node n (map (abstractTerm i t) ts) (abstractTerm i t t')
abstractTerm' i t (Repeat n ts) = Repeat n (map (abstractTerm i t) ts)

residualize t = residualize' t (free t)

residualize' (Free x) fv = Free x
residualize' (Binop b t u) fv = let t' = residualize' t fv
                                    u' = residualize' u fv
                                in  Binop b t' u'
residualize' (Lambda x t) fv = let x' = rename fv x
                                   t' = residualize' (subst (Free x') t) (x':fv)
                               in  Lambda x (abstract x' t')
residualize' (Con c ts) fv = Con c (map (\t -> residualize' t fv) ts)
residualize' (Apply t u) fv = let t' = residualize' t fv
                                  u' = residualize' u fv
                              in  Apply t' u'
residualize' (Case t bs) fv = let t' = residualize' t fv
                                  bs' = map (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                              xs' = take (length xs) fv'
                                                              t' = residualize' (foldr (\x t -> subst (Free x) t) t xs') fv'
                                                          in  (c,xs,foldl (\t x -> abstract x t) t' xs')) bs
                              in  Case t' bs'
residualize' (Let x t u) fv = let x' = rename fv x
                                  t' = residualize' t fv
                                  u' = residualize' (subst (Free x') u) (x':fv)
                              in  subst t' (abstract x' u')
residualize' (Node n ts t) fv = let t' = foldr (\u t -> Apply t u) (Fun n) ts
                                    u = residualize' t fv
                                in  Where t' [(n,foldl (\t x -> Lambda x (abstract x t)) u (map (\(Free x) -> x) ts))]
residualize' (Repeat n ts) fv = foldr (\u t -> Apply t u) (Fun n) ts

unfold t d = unfold' t EmptyCtx d

unfold' (Fun f) k d = case (lookup f d) of
                         Nothing -> error ("Undefined function: "++f)
                         Just t' -> (place t' k,d)
unfold' (Binop b t u) k d = unfold' t (Leftop b k u) d
unfold' (Apply t u) k d = unfold' t (ApplyCtx k u) d
unfold' (Case t bs) k d = unfold' t (CaseCtx k bs) d
unfold' (Where t ds) k d = unfold' t k (ds++d)
unfold' t k d = (place t k,d)

rename fv x = if   x `elem` fv
              then rename fv (x++"'")
              else x

renameList fv = let x = rename fv "x"
                in  x:(renameList (x:fv))

stripLambda (Lambda x t) = let x' = rename (free t) x
                               (xs,u) = stripLambda (subst (Free x') t)
                           in  (x':xs,u)
stripLambda t = ([],t)

blank = Text.PrettyPrint.HughesPJ.space

prettyTerm (Free x) = text x
prettyTerm (Bound i) = (text "#") <> (int i)
prettyTerm (Binop b t u) = (prettyAtom t) <+> (text b) <+> (prettyAtom u)
prettyTerm t@(Lambda _ _) = let (xs,t') = stripLambda t
                            in  (text "\\") <> (hsep (map text xs)) <> (text ".") <> (prettyTerm t')
prettyTerm t@(Con c ts) = if   isNat t
                          then int (con2nat t)
                          else if isList t
                               then text "[" <> (hcat (punctuate comma (map prettyTerm (con2list t)))) <> (text "]")
                               else if ts==[]
                                    then text c
                                    else (text c) <> (parens (hcat (punctuate comma (map prettyTerm ts))))
prettyTerm t@(Apply _ _) = prettyApp t
prettyTerm (Fun f) = text f
prettyTerm (Case t (b:bs)) = hang ((text "case") <+> (prettyAtom t) <+> (text "of")) 1 (blank <+> (prettyBranch b) $$ (vcat (map (\b->(text "|" <+>) (prettyBranch b)) bs))) where
   prettyBranch (c,[],t) = (text c) <+> (text "->") <+> (prettyTerm t)
   prettyBranch (c,xs,t) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (free t) xs
                               xs' = take (length xs) fv
                               t' = foldr (\x t->subst (Free x) t) t xs'
                           in  (text c) <> (parens (hcat (punctuate comma (map text xs')))) <+> (text "->") <+> (prettyTerm t') $$ empty
prettyTerm (Let x t u) = let x' = rename (free u) x
                         in  ((text "let") <+> (text x') <+> (text "=") <+> (prettyTerm t)) $$ ((text "in") <+> (prettyTerm (subst (Free x') u)))
prettyTerm (Where t ds) = (prettyTerm t) $$ (text "where") $$ (prettyEnv ds)
prettyTerm (Node n ts t) = (text n) <+> (hsep (map prettyTerm ts)) <+> (text "=") <+> (prettyTerm t)
prettyTerm (Repeat n ts ) = (text n) <+> (hsep (map prettyTerm ts))

prettyApp (Apply t u) = (prettyApp t) <+> (prettyAtom u)
prettyApp t = prettyAtom t

prettyAtom (Free x) = text x
prettyAtom t@(Con c ts) = if   isNat t
                          then int (con2nat t)
                          else if isList t
                               then text "[" <> (hcat (punctuate comma (map prettyTerm  (con2list t)))) <> (text "]")
                               else if ts==[]
                                    then text c
                                    else (text c) <> (parens (hcat (punctuate comma (map prettyTerm ts))))
prettyAtom (Fun f) = text f
prettyAtom t = parens (prettyTerm t)

prettyEnv [(x,t)] = (text x) <+> equals <+> (prettyTerm t)
prettyEnv ((x,t):ds) = (text x) <+> equals <+> (prettyTerm t) <> semi $$ (prettyEnv ds)

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con (n-1)]

con2nat (Con "Zero" [])  = 0
con2nat (Con "Succ" [n]) = 1+con2nat n

potDef = emptyDef
         { commentStart    = "/*"
         , commentEnd      = "*/"
         , commentLine     = "--"
         , nestedComments  = True
         , identStart      = lower
         , identLetter     = do letter <|> oneOf "_'"
         , reservedNames   = ["case","of","where","let","in","ALL","EX","ANY"]
         , reservedOpNames = ["~","/\\","\\/","<=>","=>","+","-","*","/"]
         , caseSensitive   = True
         }

lexer = T.makeTokenParser potDef

symbol     = T.symbol lexer
bracks     = T.parens lexer
semic      = T.semi lexer
comm       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
natural    = T.natural lexer

con = do
      c <- upper
      cs <- many letter
      return (c:cs)

makeWhere t [] = t
makeWhere t fs = let (fn,_) = unzip fs
                 in  makeFuns fn (Where t fs)

makeFuns fn (Free x) = if x `elem` fn then Fun x else Free x
makeFuns fn (Bound i ) = Bound i
makeFuns fn (Binop b t u) = Binop b (makeFuns fn t) (makeFuns fn u)
makeFuns fn (Lambda x t) = Lambda x (makeFuns fn t)
makeFuns fn (Con c ts) = Con c (map (makeFuns fn) ts)
makeFuns fn (Apply t u) = Apply (makeFuns fn t) (makeFuns fn u)
makeFuns fn (Fun f) = Fun f
makeFuns fn (Case t bs) = Case (makeFuns fn t) (map (\(c,xs,t) -> (c,xs,makeFuns fn t)) bs)
makeFuns fn (Let x t u) = Let x (makeFuns fn t) (makeFuns fn u)
makeFuns fn (Where t ds) = Where (makeFuns fn t) (map (\(x,t) -> (x,makeFuns fn t)) ds)

prog = do
       e <- expr
       fs <-     do
                 reserved "where"
                 fs <- sepBy1 fundef semic
                 return fs
             <|> do
                 spaces
                 return []
       return (makeWhere e fs)

fundef = do
         f <- identifier
         symbol "="
         e <- expr
         return (f,e)

expr = buildExpressionParser prec term

prec = [ [ unop "~" (Fun "not")],
         [ op "/\\" (Fun "and") AssocRight ],
         [ op "\\/" (Fun "or") AssocRight ],
         [ op "<=>" (Fun "iff") AssocRight ],
         [ op "=>" (Fun "implies") AssocRight ]
       ]
       where
       op o t assoc   = Infix (do
                               reservedOp o
                               return (\x y -> Apply (Apply t x) y)
                              ) assoc
       unop o t       = Prefix (do
                                reservedOp o
                                return (\x -> Apply t x)
                               )

term =     do
           a <- atom
           e <-      do
                     reservedOp "+"
                     a' <- atom
                     return (Binop "+" a a')
                 <|> do
                     reservedOp "-"
                     a' <- atom
                     return (Binop "-" a a')
                 <|> do
                     reservedOp "*"
                     a' <- atom
                     return (Binop "*" a a')
                 <|> do
                     reservedOp "/"
                     a' <- atom
                     return (Binop "/" a a')
                 <|> do
                     as <- many atom
                     return (foldl Apply a as)
           return e
       <|> do
           symbol "\\"
           xs <- many1 identifier
           symbol "."
           e <- expr
           return (foldr (\x t->Lambda x (abstract x t)) e xs)
       <|> do
           reserved "case"
           e <- expr
           reserved "of"
           bs <- sepBy1 branch (symbol "|")
           return (Case e bs)
       <|> do
           reserved "let"
           x <- identifier
           symbol "="
           e1 <- expr
           reserved "in"
           e2 <- expr
           return (Let x e1 (abstract x e2))

atom =     do
           x <- identifier
           return (Free x)
       <|> do
           c <- con
           es <-     do
                     es <- bracks (sepBy1 expr comm)
                     return es
                 <|> do
                     spaces
                     return []
           return (Con c es)
       <|> do
           n <- natural
           return (nat2con n)
       <|> do
           symbol "["
           ts <- sepBy expr comm
           symbol "]"
           return (list2con ts)
       <|> do
           e <- bracks expr
           return e

branch = do
         c <- con
         xs <-     do
                   xs <- bracks (sepBy1 identifier comm)
                   return xs
               <|> do
                   spaces
                   return []
         symbol "->"
         e <- expr
         return (c,xs,foldl (\t x -> abstract x t) e xs)

parseExpr input = parse expr "(ERROR)" input

parseProg input = parse prog "(ERROR)" input


