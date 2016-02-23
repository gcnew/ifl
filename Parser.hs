{-# OPTIONS_GHC -Wall #-}

module Parser where

import Data.Char (isDigit, isAlpha)
import Prelude hiding (pred)

import AST
import Lexer

type Parser a = [Token] -> [(a, [Token])]
data PartialExpr = NoOp | FoundOp Name CoreExpr

pLit :: String -> Parser String
pLit s = pSat (== s)
-- pLit = pSat . (==)

keywords :: [String]
keywords = [ "let", "letrec", "case", "in", "of", "Pack" ]

pVar :: Parser String
pVar = pSat isVar
    where isVar s = not (s `elem` keywords) && isAlpha (head s)
       -- isVar = and . (`map` [ isAlpha . head, not . (`elem` keywords) ]) . (flip ($))

pNum :: Parser Int
pNum = pSat (and . (map isDigit)) `pApply` read

pSat :: (String -> Bool) -> Parser String
pSat _ [] = []
pSat pred ((_, val) : xs) | pred val  = [(val, xs)]
                          | otherwise = []

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 tokens = (p1 tokens) ++ (p2 tokens)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen comb p1 p2 toks = [ (comb v1 v2, toks2) | (v1, toks1) <- p1 toks,
                                                (v2, toks2) <- p2 toks1 ]

pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 comb p1 p2 p3 toks = [ (comb v1 v2 v3, toks3) | (v1, toks1) <- p1 toks,
                                                       (v2, toks2) <- p2 toks1,
                                                       (v3, toks3) <- p3 toks2 ]

pThen4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 comb p1 p2 p3 p4 toks = [ (comb v1 v2 v3 v4, toks4) | (v1, toks1) <- p1 toks,
                                                             (v2, toks2) <- p2 toks1,
                                                             (v3, toks3) <- p3 toks2,
                                                             (v4, toks4) <- p4 toks3 ]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (pEmpty [])

pEmpty :: a -> Parser a
pEmpty val toks = [(val, toks)]

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p toks = [ ((v1 : vn), toksn) | (v1, toks1) <- p toks,
                                           (vn, toksn) <- pZeroOrMore p toks1]

pApply :: Parser a -> (a -> b) -> Parser b
pApply p tranf toks = [ (tranf v, newToks) | (v, newToks) <- p toks ]

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep p sep = pThen (:) p (pZeroOrMore parseMore)
    where parseMore = pThen (\_ x -> x) sep p

syntax :: [Token] -> CoreProgram
syntax = takeFirstParse . pProgram
    where takeFirstParse ((prog, []) : _) = prog
          takeFirstParse (_ : others)     = takeFirstParse others
          takeFirstParse _                = error "Syntax error"

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc = pThen4 mkSc pVar (pZeroOrMore pVar) (pLit "=") pExpr
    where mkSc fn params _ expr = (fn, params, expr)

pExpr :: Parser CoreExpr
pExpr = pLet `pAlt` pCase `pAlt` pLambda `pAlt` pExprOr

pExprOr,  pExprAnd,  pExprRel,  pExprTerm,  pExprFactor  :: Parser CoreExpr
pExprOrC, pExprAndC, pExprRelC, pExprTermC, pExprFactorC :: Parser PartialExpr

pExprOr  = pThen assembleOp pExprAnd pExprOrC
pExprOrC = pThen FoundOp (pLit "|") pExprOr `pAlt` (pEmpty NoOp)

pExprAnd  = pThen assembleOp pExprRel pExprAndC
pExprAndC = pThen FoundOp (pLit "&") pExprAnd `pAlt` (pEmpty NoOp)

relOps :: [String]
relOps = [ "<", "<=", "==", "/=", ">=", ">" ]

pRelOp :: Parser String
pRelOp = pSat (`elem` relOps)

pExprRel  = pThen assembleOp pExprTerm pExprRelC
pExprRelC = pThen FoundOp pRelOp pExprRel `pAlt` (pEmpty NoOp)

pExprTerm  = pThen assembleOp pExprFactor pExprTermC
pExprTermC = pThen FoundOp (pLit "+") pExprTerm
      `pAlt` pThen FoundOp (pLit "-") pExprTerm
      `pAlt` (pEmpty NoOp)

pExprFactor  = pThen assembleOp pExprAp pExprFactorC
pExprFactorC = pThen FoundOp (pLit "*") pExprFactor
        `pAlt` pThen FoundOp (pLit "/") pExprFactor
        `pAlt` (pEmpty NoOp)

pExprAp :: Parser CoreExpr
pExprAp = pOneOrMore pAExpr `pApply` mkApChain
    where mkApChain = foldl1 EAp

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp expr NoOp = expr
assembleOp lhs (FoundOp op rhs) = EAp (EAp (EVar op) lhs) rhs

pLet :: Parser CoreExpr
pLet = pThen4 mkLet pLetOrLetRec pDefns (pLit "in") pExpr
    where pLetOrLetRec :: Parser String
          pLetOrLetRec = (pLit "letrec") `pAlt` (pLit "let")

          mkLet :: String -> [CoreLetDefn] -> String -> CoreExpr -> CoreExpr
          mkLet lit defns _ expr = ELet (isRec lit) defns expr

          isRec :: String -> Bool
          isRec "letrec" = True
          isRec "let"    = False
          isRec _        = error "Programming error"

pDefns :: Parser [CoreLetDefn]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")

pDefn :: Parser CoreLetDefn
pDefn = pThen3 mkDefn pVar (pLit "=") pExpr
    where mkDefn v _ e = (v, e)

pCase :: Parser CoreExpr
pCase = pThen4 mkCase (pLit "case") pExpr (pLit "of") pAlters
    where mkCase _ expr _ alts = ECase expr alts

pAlters :: Parser [CoreAlt]
pAlters = pOneOrMoreWithSep pAlter (pLit ";")

pAlter :: Parser CoreAlt
pAlter = pThen4 mkAlter pVal (pZeroOrMore pVar) (pLit "->") pExpr
    where pVal = pThen3 (\_ x _ -> x) (pLit "<") pNum (pLit ">")
          mkAlter val vars _ expr = (val, vars, expr)

pLambda :: Parser CoreExpr
pLambda = pThen4 mkLambda (pLit "\\") (pOneOrMore pVar) (pLit ".") pExpr
    where mkLambda _ vars _ expr = ELam vars expr

pAExpr :: Parser CoreExpr
pAExpr = (pVar `pApply` EVar)
  `pAlt` (pNum `pApply` ENum)
  `pAlt` (pThen4 (\_ _ x _ -> x) (pLit "Pack") (pLit "{") pTagArity (pLit "}"))
  `pAlt` (pThen3 (\_ x _ -> x) (pLit "(") pExpr (pLit ")"))
  where pTagArity = pThen3 (\tag _ arity -> EConstr tag arity) pNum (pLit ",") pNum

parse :: String -> CoreProgram
parse = syntax . (clex 1)
