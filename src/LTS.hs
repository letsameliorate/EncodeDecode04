{- LTS Definition -}

module LTS where

import Data.Char
import Data.Maybe
import Data.List (intersect,(\\),zip4)
import Data.Foldable (foldrM,find)
import Control.Monad
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language
import Debug.Trace
import Term

data LTS = Node Term [LTS]
         | Unfold String Term LTS
         | ConElim String Term LTS
         | Function String LTS
         | Var String LTS
         | Embedding String LTS

instance Show LTS where
   show t = render (prettyLTS t)

instance Eq LTS where
   (==) l l' = eqLTS [] l l'

eqLTS c (Node t ls) (Node t' ls') | match t t' = all (\ (l,l') -> eqLTS c l l') (zip ls ls')
eqLTS c (Unfold f t l) (Unfold f' t' l') | f==f' = eqLTS c l l'
eqLTS c l (Unfold _ _ l') = eqLTS c l l'
eqLTS c (ConElim c' _ l) (ConElim c'' _ l') | c'==c'' = eqLTS c l l'
eqLTS c l (ConElim _ _ l') = eqLTS c l l'
eqLTS c (Function f l) (Function f' l') = eqLTS ((f,f'):c) l l'
eqLTS c (Var x l) (Var x' l') = eqLTS c l l'
eqLTS c (Embedding f l) (Embedding f' l') = (f,f') `elem` c
eqLTS c l l' = False

renameLTS l l' = isJust (renameLTS' [] (renamebvs l) (renamebvs l') [])

renamebvs l = let bvs = boundLTS l
                  fvs = foldr (\b fvs -> let x' = rename fvs "x" in x':fvs) (freeLTS l) bvs
                  xs = take (length bvs) fvs
              in  foldr (\x l -> substLTS (Node (Free x) []) l) l xs

renameLTS' c (Node (Free x) []) (Node (Free x') []) r = if   x `elem` fst (unzip r)
                                                        then if   (x,x') `elem` r then Just r else Nothing
                                                        else Just ((x,x'):r)
renameLTS' c (Node t ls) (Node t' ls') r | match t t' = foldrM (\ (l,l') r -> renameLTS' c l l' r) r (zip ls ls')
renameLTS' c (Unfold f t l) (Unfold f' t' l') r | f==f' = renameLTS' c l l' r
renameLTS' c l (Unfold _ _ l') r = renameLTS' c l l' r
renameLTS' c (ConElim c' _ l) (ConElim c'' _ l') r | c'==c'' = renameLTS' c l l' r
renameLTS' c l (ConElim _ _ l') r = renameLTS' c l l' r
renameLTS' c (Function f l) (Function f' l') r = renameLTS' ((f,f'):c) l l' r
renameLTS' c (Var x l) (Var x' l') r = if   x `elem` fst (unzip r)
                                       then if   (x,x') `elem` r then Just r else Nothing
                                       else Just ((x,x'):r)
renameLTS' c (Embedding f l) (Embedding f' l') r | (f,f') `elem` c = Just r
renameLTS' c t t' r = Nothing

instanceLTS c (Node (Free x) []) (Node (Free x') []) s = if   x `elem` fst (unzip s)
                                                         then if   (x,Node (Free x') []) `elem` s then Just s else Nothing
                                                         else Just ((x,Node (Free x') []):s)
instanceLTS c (Node (Free x) []) l s | x `elem` (freeLTS l) = if x `elem` fst (unzip s)
                                                              then if (x,l) `elem` s then Just s else Nothing
                                                              else Just ((x,l):s)
instanceLTS c (Node t ls) (Node t' ls') s | match t t' = foldrM (\ (l,l') s -> instanceLTS c l l' s) s (zip ls ls')
instanceLTS c (Unfold f t l) (Unfold f' t' l') s | f==f' = instanceLTS c l l' s
instanceLTS c l (Unfold _ _ l') s = instanceLTS c l l' s
instanceLTS c (ConElim c' _ l) (ConElim c'' _ l') s | c'==c'' = instanceLTS c l l' s
instanceLTS c l (ConElim _ _ l') s = instanceLTS c l l' s
instanceLTS c (Function f l) (Function f' l') s = instanceLTS ((f,f'):c) l l' s
instanceLTS c (Embedding f l) (Embedding f' l') s | (f,f') `elem` c = Just s
instanceLTS c (Var x _) l s = if   x `elem` fst (unzip s)
                              then if (x,l) `elem` s then Just s else Nothing
                              else if x `elem` genvars l then Just ((x,l):s) else Nothing
instanceLTS c t t' s = Nothing

embedLTS l l' = coupleLTS [] l l' []

embeddingLTS c l l' r = mplus (coupleLTS c l l' r) (diveLTS c l l' r)

coupleLTS c (Node (Free x) []) (Node (Free x') []) r = if   x `elem` fst (unzip r)
                                                       then if (x,x') `elem` r then Just r else Nothing
                                                       else Just ((x,x'):r)
coupleLTS c (Node t ls) (Node t' ls') r | match t t' = foldrM (\ (l,l') r -> embeddingLTS c l l' r) r (zip ls ls')
coupleLTS c (Unfold f t l) (Unfold f' t' l') r | f==f' = embeddingLTS c l l' r
coupleLTS c (ConElim c' _ l) (ConElim c'' _ l') r | c'==c'' = embeddingLTS c l l' r
coupleLTS c (Function f l) (Function f' l') r = embeddingLTS ((f,f'):c) l l' r
coupleLTS c (Var x l) (Var x' l') r = if   x `elem` fst (unzip r)
                                      then if (x,x') `elem` r then Just r else Nothing
                                      else Just ((x,x'):r)
coupleLTS c (Embedding f l) (Embedding f' l') r = if   f `elem` fst (unzip c)
                                                  then if (f,f') `elem` c then Just r else Nothing
                                                  else embeddingLTS c l l' r
coupleLTS c t u r = Nothing

diveLTS c l (Node _ ls) r = msum (map (\l' -> embeddingLTS c l l' r) ls)
diveLTS c l (Unfold f t l') r = embeddingLTS c l l' r
diveLTS c l (ConElim c' _ l') r = embeddingLTS c l l' r
diveLTS c l (Function f l') r = embeddingLTS c l l' r
diveLTS c l (Var x l') r = embeddingLTS c l l' r
diveLTS c l (Embedding f l') r = Nothing

generaliseLTS l l' fv s = generaliseLTS' [(True,(l,l'))] fv s

generaliseLTS' [] fv s = []
generaliseLTS' ((c,(l,l')):cls) fv s = if   isJust (coupleLTS [] l' l [])
                                       then if   c
                                            then let gls = generaliseLTS' (cls++map (\ll -> (True,ll)) (zip (subtrees l) (subtrees l'))) fv s
                                                     (ls,ls') = splitAt (length cls) gls
                                                 in (replaceSubtrees l ls'):ls
                                            else case (find (\ (x,l'') -> renameLTS l'' l) s) of
                                                    Just (x,l'') -> let gls = generaliseLTS' (cls++map (\ll -> (True,ll)) (zip (subtrees l) (subtrees l'))) fv s
                                                                        (ls,ls') = splitAt (length cls) gls
                                                                    in  (Var x (replaceSubtrees l ls')):ls
                                                    Nothing -> let x = rename (fv++fst(unzip s)) "x"
                                                                   gls = generaliseLTS' (cls++map (\ll -> (True,ll)) (zip (subtrees l) (subtrees l'))) fv ((x,l):s)
                                                                   (ls,ls') = splitAt (length cls) gls
                                                               in  (Var x (replaceSubtrees l ls')):ls
                                       else let gls = generaliseLTS' (cls++map (\l'' -> (False,(l'',l'))) (subtrees l)) fv s
                                                (ls,ls') = splitAt (length cls) gls
                                            in (replaceSubtrees l ls'):ls

subtrees (Node t ls) = ls
subtrees (Unfold f t l) = [l]
subtrees (ConElim c t l) = [l]
subtrees (Function f l) = [l]
subtrees (Var x l) = [l]
subtrees (Embedding f l) = [l]

replaceSubtrees (Node t _) ls = Node t ls
replaceSubtrees (Unfold f t _) [l] = Unfold f t l
replaceSubtrees (ConElim c t _) [l] = ConElim c t l
replaceSubtrees (Function f _) [l] = Function f l
replaceSubtrees (Var x _) [l] = Var x l
replaceSubtrees (Embedding f _) [l] = Embedding f l

root (Node t ls) = t
root (Unfold f t l) = t
root (ConElim c t l) = t
root (Function f l) = root l
root (Var x l) = root l
root (Embedding f l) = root l

freeLTS l = freeLTS' [] l

freeLTS' xs (Node (Free x) []) = if x `elem` xs then xs else x:xs
freeLTS' xs (Node t ls) = foldr (\l xs -> freeLTS' xs l) xs ls
freeLTS' xs (Unfold f t l) = freeLTS' xs l
freeLTS' xs (ConElim c _ l) = freeLTS' xs l
freeLTS' xs (Function f l) = freeLTS' xs l
freeLTS' xs (Var x l) = freeLTS' xs l
freeLTS' xs (Embedding f l) = xs

genvars l = genvars' [] l

genvars' xs (Node (Free x) []) = xs
genvars' xs (Node t ls) = foldr (\l xs -> genvars' xs l) xs ls
genvars' xs (Unfold f t l) = genvars' xs l
genvars' xs (ConElim c _ l) = genvars' xs l
genvars' xs (Function f l) = genvars' xs l
genvars' xs (Var x l) = if x `elem` xs then xs else x:xs
genvars' xs (Embedding f l) = xs

boundLTS l = boundLTS' 0 [] l

boundLTS' d bs (Node (Bound i) []) = let b = i-d
                                     in  if (b<0) || (b `elem` bs) then bs else b:bs
boundLTS' d bs (Node (Lambda x t) [l]) = boundLTS' (d+1) bs l
boundLTS' d bs (Node (Case t bs') (l:ls)) = foldr (\((c,xs,t),l) bs -> boundLTS' (d+length xs) bs l) (boundLTS' d bs l) (zip bs' ls)
boundLTS' d bs (Node (Let x t u)  [l,l']) = boundLTS' (d+1) (boundLTS' d bs l) l'
boundLTS' d bs (Node t ls) = foldr (\l bs -> boundLTS' d bs l) bs ls
boundLTS' d bs (Unfold f t l) = boundLTS' d bs l
boundLTS' d bs (ConElim c _ l) = boundLTS' d bs l
boundLTS' d bs (Function f l) = boundLTS' d bs l
boundLTS' d bs (Var x l) = bs
boundLTS' d bs (Embedding f l) = bs

abstractLTS x l = abstractLTS' 0 x l
abstractLTS' i x (Node (Free x') []) = if x==x' then Node (Bound i) [] else Node (Free x') []
abstractLTS' i x (Node (Bound i') []) = if i'>=i then Node (Bound (i'+1)) [] else Node (Bound i') []
abstractLTS' i x (Node (Lambda x' t) [l]) = Node (Lambda x' t) [abstractLTS' (i+1) x l]
abstractLTS' i x (Node (Case t bs) (l:ls)) = Node (Case t bs) ((abstractLTS' i x l):(map (\((c,xs,t),l) -> abstractLTS' (i + length xs) x l) (zip bs ls)))
abstractLTS' i x (Node (Let x' t u) [l,l']) = Node (Let x' t u) [abstractLTS' i x l,abstractLTS' (i+1) x l']
abstractLTS' i x (Node t ls) = Node t (map (abstractLTS' i x) ls)
abstractLTS' i x (Unfold f t l) = Unfold f t (abstractLTS' i x l)
abstractLTS' i x (ConElim c t l) = ConElim c t (abstractLTS' i x l)
abstractLTS' i x (Function f l) = Function f (abstractLTS' i x l)
abstractLTS' i x (Var x' l) = Var x' (abstractLTS' i x l)
abstractLTS' i x (Embedding f l) = Embedding f (abstractLTS' i x l)

substLTS l l' = substLTS' 0 l l'
substLTS' i l (Node (Free x') []) = Node (Free x') []
substLTS' i l (Node (Bound i') []) = if   i'<i
                                     then Node (Bound i') []
                                     else if   i'==i
                                          then l
                                          else Node (Bound (i'-1)) []
substLTS' i l (Node (Lambda x t) [l']) = Node (Lambda x t) [substLTS' (i+1) l l']
substLTS' i l (Node (Case t bs) (l':ls)) = Node (Case t bs) ((substLTS' i l l'):(map (\((c,xs,t),l') -> substLTS' (i+length xs) l l')) (zip bs ls))
substLTS' i l (Node (Let x t u) [l',l'']) = Node (Let x t u) [substLTS' i l l',substLTS' (i+1) l l'']
substLTS' i l (Node t ls) = Node t (map (substLTS' i l) ls)
substLTS' i l (Unfold f t l') = Unfold f t (substLTS' i l l')
substLTS' i l (ConElim c t l') = ConElim c t (substLTS' i l l')
substLTS' i l (Function f l') = Function f (substLTS' i l l')
substLTS' i l (Embedding f l') = Embedding f (substLTS' i l l')

embeddings es (Node _ ls) = foldr (\l es -> embeddings es l) es ls
embeddings es (Unfold _ _ l) = embeddings es l
embeddings es (ConElim _ _ l) = embeddings es l
embeddings es (Function f l) = embeddings es l
embeddings es (Var x l) = embeddings es l
embeddings es (Embedding e _) = if e `elem` es then es else e:es

stripAbs (Node (Lambda x t) [l]) = let x' = rename (freeLTS l) x
                                       (xs,l') = stripAbs (substLTS (Node (Free x') []) l)
                                   in  (x':xs,l')
stripAbs l = ([],l)

prettyLTS (Node (Free x) []) = text x
prettyLTS (Node (Bound i) []) = (text "#") <> (int i)
prettyLTS l@(Node (Lambda _ _) _) = let (xs,l') = stripAbs l
                                    in  (text "\\") <> (hsep (map text xs)) <> (text ".") <> (prettyLTS l')
prettyLTS (Node (Con c _) ls) = if ls==[] then text c
                                          else (text c) <> (parens (hcat (punctuate comma (map prettyLTS ls))))
prettyLTS (Node (Apply _ _) [l,l']) = (prettyLTS l) <+> (prettyLTS l')
prettyLTS (Node (Case t (b:bs)) (l:l':ls)) = hang ((text "case") <+> (prettyArg l) <+> (text "of")) 1 (blank <+> (prettyBranch (b,l')) $$ (vcat (map (\(b,l) -> (text "|" <+>) (prettyBranch (b,l))) (zip bs ls)))) where
   prettyBranch ((c,[],t),l) = (text c) <+> (text "->") <+> (prettyLTS l)
   prettyBranch ((c,xs,t),l) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (freeLTS l) xs
                                   xs' = take (length xs) fv
                                   l' = foldr (\x l -> substLTS (Node (Free x) []) l) l xs'
                               in  (text c) <> (parens (hcat (punctuate comma (map text xs')))) <+> (text "->") <+> (prettyLTS l') $$ empty
prettyLTS (Node (Let x t u) [l,l']) = let x' = rename (freeLTS l') x
                                      in   ((text "let") <+> (text x') <+> (text "=") <+> (prettyLTS l)) $$ ((text "in") <+> (prettyLTS (substLTS (Node (Free x') []) l')))
prettyLTS (Unfold f t l) = (text ("-"++f++"->")) <+> (prettyLTS l)
prettyLTS (ConElim c _ l) = (text ("-"++c++"->")) <+> (prettyLTS l)
prettyLTS (Function f l) = (text (f++":")) <+> (prettyLTS l)
prettyLTS (Var x l) = (text (x++":")) <+> (prettyLTS l)
prettyLTS (Embedding f l) = text f

prettyArg (Node (Free x) []) = text x
prettyArg (Node (Bound i) []) = (text "#") <> (int i)
prettyArg (Node (Con c _) ls) = if ls==[] then text c
                                          else (text c) <> (parens (hcat (punctuate comma (map prettyLTS ls))))
prettyArg l = parens (prettyLTS l)

drawLTS l = render ((text "digraph G {\norientation=landscape\nratio=compress;\nsize=\"10,6\"\n") <> (drawLTS' "1" [] l) <> (text "}"))
drawLTS' n d (Node (Free x) ls) = (text ("\"" ++ n ++ "\"[shape=box label = \"\"]\n")) <> (text ("\"" ++ (n ++ "0") ++ "\"[shape=box label = \"\"]\n"))
                                  <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "0") ++ "\"[label = \"" ++ x ++ "\"]\n"))
                                  <> (hcat (map (\(i,l) -> (drawLTS' (n++(show i)) d l) <> (text ("\"" ++ n ++ "\"->\"" ++ (n++(show i)) ++ "\"[label = \"#" ++ (show i) ++ "\"]\n"))) (zip [1..] ls)))
drawLTS' n d (Node (Bound i) ls) = (text ("\"" ++ n ++ "\"[shape=box label = \"\"]\n")) <> (text ("\"" ++ (n ++ "0") ++ "\"[shape=box label = \"\"]\n"))
                                   <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "0") ++ "\"[label = \"" ++ (show i) ++ "\"]\n"))
                                   <> (hcat (map (\(i,l) -> (drawLTS' (n++(show i)) d l) <> (text ("\"" ++ n ++ "\"->\"" ++ (n++(show i)) ++ "\"[label = \"#" ++ (show i) ++ "\"]\n"))) (zip [1..] ls)))
drawLTS' n d (Node (Lambda x t) [l]) = let x' = rename (freeLTS l) x
                                       in  (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "1") d (substLTS (Node (Free x') []) l)) <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "1") ++ "\"[label = \\" ++ x' ++ "\"]\n"))
drawLTS' n d (Node (Con c ts) ls) = (text ("\"" ++ n ++ "\"[shape=box label = \"\"]\n")) <> (text ("\"" ++ (n ++ "0") ++ "\"[shape=box label = \"\"]\n"))
                                    <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "0") ++ "\"[label = \"" ++ c ++ "\"]\n"))
                                    <> (hcat (map (\(i,l) -> (drawLTS' (n++(show i)) d l) <> (text ("\"" ++ n ++ "\"->\"" ++ (n++(show i)) ++ "\"[label = \"#" ++ (show i) ++ "\"]\n"))) (zip [1..] ls)))
drawLTS' n d (Node (Case t bs) (l:ls)) = (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "0") d l)
                                         <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "0") ++ "\"[label = \"case\"]\n"))
                                         <> (hcat (map (\(i,(c,xs,t),l) -> let xs' = map (rename (freeLTS l)) xs
                                                                               l' = foldr (\x l -> substLTS (Node (Free x) []) l) l xs'
                                                                           in  (drawLTS' (n++(show i)) d l') <> (text ("\"" ++ n ++ "\"->\"" ++ (n++(show i)) ++ "\"[label = \"" ++ (show (Con c (map Free xs'))) ++ "\"]\n"))) (zip3 [1..] bs ls)))
drawLTS' n d (Node (Let x t u) [l,l']) = let x' = rename (freeLTS l') x
                                         in  (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "1") d l) <> (drawLTS' (n ++ "2") d (substLTS (Node (Free x') []) l'))
                                             <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "1") ++ "\"[shape=box label = \"@\"]\n")) <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "2") ++ "\"[shape=box label = \"\\" ++ x' ++ "\"]\n"))
drawLTS' n d (Unfold f t l) = (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "1") d l)
                              <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "1") ++ "\"[label = \"tau_" ++ f ++ "\"]\n"))
drawLTS' n d (ConElim c t l) = (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "1") d l)
                               <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "1") ++ "\"[label = \"tau_" ++ c ++ "\"]\n"))
drawLTS' n d (Function f l) = (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (drawLTS' (n ++ "1") ((f,n):d) l)
                              <> (text ("\"" ++ n ++ "\"->\"" ++ (n ++ "1") ++ "\"[label = \"\"]\n"))
drawLTS' n d (Embedding f l) = case (lookup f d) of
                                Nothing -> drawLTS' n d l
                                Just n' -> (text ("\"" ++ n ++ "\"[shape=box label=\"\"]\n")) <> (text ("\"" ++ n ++ "\"->\"" ++ n' ++ "\"[style=dotted]"))
