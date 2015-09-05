module Context where

import Term

data Context = EmptyCtx
             | ApplyCtx Context Term
             | CaseCtx Context [(String,[String],Term)] deriving Show

place e EmptyCtx = e
place e (ApplyCtx con t) = place (Apply e t) con
place e (CaseCtx con bs) = place (Case e bs) con

