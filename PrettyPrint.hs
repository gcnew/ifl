module PrettyPrint where

import Iseq
import AST

operators :: [String]
operators = map (:[]) "+-*/"

-- TODO: operator precedence / parens
pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v)    = iStr v
pprExpr (ENum num)  = iNum num

pprExpr (EAp (EAp (EVar op) e1) e2)
    | op `elem` operators = iConcat [ pprAExpr e1, iStr " ", iStr op, iStr " ", pprAExpr e2 ]
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprAExpr e2)

pprExpr (EConstr tag arity)
    = iConcat [ iStr "Pack{",
                iNum tag, iStr ", ",
                iNum arity, iStr "}" ]

pprExpr (ELet isrec defns expr)
    = iConcat [ iStr keyword,
                iStr " ", iIndent (pprDefns defns), iNewline,
                iStr "in ", pprExpr expr ]
    where keyword | isrec     = "letrec"
                  | otherwise = "let"

pprExpr (ELam vars expr) = iConcat [ iStr "\\ ", (pprVarNames vars), iStr ". ", pprExpr expr ]

pprExpr (ECase expr alts)
    = iConcat [ iStr "case ", pprExpr expr, iStr " of ",
                iIndent (iNewline `iAppend` pprAlts alts) ]

pprAlts :: [CoreAlt] -> Iseq
pprAlts alts = iInterleave iNewline (map pprAlt alts)

pprAlt :: CoreAlt -> Iseq
pprAlt (tag, vars, expr)
    = iConcat [ iStr "<", iNum tag, iStr "> ",
                pprVarNames vars, iStr " -> ", pprExpr expr ]

pprAExpr :: CoreExpr -> Iseq
pprAExpr e
    | isAtomicExpr e = pprExpr e
    | otherwise      = (iStr "(") `iAppend` pprExpr e `iAppend` (iStr ")")

pprDefns :: [(Name,CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
    where sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]

pprProgram :: CoreProgram -> Iseq
pprProgram prog = iInterleave (iStr "\n\n") (map pprScDefn prog)

pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, vars, expr) = iConcat [ iStr name, iStr " ", pprVarNames vars,
                                         iStr " = " , iIndent (pprExpr expr) ]

pprVarNames :: [String] -> Iseq
pprVarNames names = iInterleave (iStr " ") (map iStr names)

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)
