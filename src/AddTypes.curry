------------------------------------------------------------------
-- A tool to add all those type signatures, you didn't bother to 
-- write while developing the program. 
--
-- @author Bernd Brassel, with changes by Michael Hanus
-- @version April 2021
-- 
-- Possible extensions: Use type synonyms to reduce annotations
------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module AddTypes ( main, addTypeSignatures )
 where

import Control.Monad      ( when )
import Data.List
import System.Environment ( getArgs )

import AbstractCurry.Types
import AbstractCurry.Files
import AbstractCurry.Pretty
import Control.AllValues         ( getOneValue )
import Control.Monad.Trans.State
import System.CurryPath          ( runModuleAction )
import System.Process            ( exitWith, system )
import Text.Pretty

import CurryStringClassifier

-- The tool is rather simple, it uses Curry's facilities for 
-- meta-programming to read the program in the form defined 
-- in the AbstractCurry module. 
-- The libraries for meta-programming provides commands to read
-- AbstractCurry programs typed and untyped.
-- By comparing the results of these two operations, we are able to
-- distinguish the inferred types from those given by the programmer.
-- 
-- addtypes makes use of the CurryStringClassifier, cf. function addTypes.


--- addtypes is supposed to get its argument, the file to add type signatures
--- to from the shell. 
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-h"]       -> printUsage
    ["--help"]   -> printUsage
    ["-?"]       -> printUsage
    ["-p",fname] -> runModuleAction (writeWithTypeSignatures False) fname
    [fname]      -> runModuleAction (writeWithTypeSignatures True)  fname
    _            -> printUsage >> exitWith 1

printUsage :: IO ()
printUsage = putStrLn $ unlines
  [ "A tool to add missing type signatures to top-level operations"
  , ""
  , "Usage: curry-addtypes [-p] <Curry module>"
  , ""
  , "-p : print new program source but do not replace source file"
  ]

--- The given file is read three times: a) typed, to get all the necessary 
--- type information b) untyped to find out, which of the types were 
--- specified by the user and c) as a simple string to which the signatures
--- are added.
--- If the first argument is `True`, addtypes will write a backup of the
--- source program to `<given filename>_ORG.curry` before replacing
--- the source program with the version with signatures,
--- otherwise the version with signatures is only printed.

writeWithTypeSignatures :: Bool -> String -> IO ()
writeWithTypeSignatures replace modname = do
   when replace $ do
     system $ "cp -p " ++ modname ++ ".curry " ++ modname ++ "_ORG.curry"
     return ()
   newprog <- addTypeSignatures modname
   if replace
     then do
       writeFile (modname ++ ".curry") newprog
       putStrLn $ "Signatures added.\nA backup of the original " ++
                  "file has been written to " ++ modname ++ "_ORG.curry"
     else putStrLn newprog

addTypeSignatures :: String -> IO String
addTypeSignatures modname = do
   typedProg   <- readCurry modname
   untypedProg <- readUntypedCurry modname
   progLines   <- readFile (modname ++ ".curry")
   -- enforce reading of complete source program before returning:
   mbprog <- getOneValue
               (unscan (addTypes (scan progLines) 
                                 (getTypes typedProg untypedProg)))
   maybe (error "AddTypes: cannot add type signatures") return mbprog


--- retrieve the functions without type signature and their type

getTypes :: CurryProg -> CurryProg -> [(String,CQualTypeExpr)]
getTypes (CurryProg _ _ _ _ _ _ funcDecls1 _)
         (CurryProg _ _ _ _ _ _ funcDecls2 _) =
  getTypesFuncDecls funcDecls1 funcDecls2
 where
  getTypesFuncDecls [] [] = []
  getTypesFuncDecls (CFunc name _ _ t1 _:fs1) (CFunc _ _ _ t2 _:fs2) 
    | isUntyped t2 = (snd name,t1) : getTypesFuncDecls fs1 fs2
    | otherwise    = getTypesFuncDecls fs1 fs2

--- addtypes implements a simple algorithm to decide where to add type 
--- information. Find the first line wich contains the function name 
--- on the left hand side and insert the type annotation before that line.
--- The problem with this algorithm is that it might get confused by 
--- comments. This is where the Curry string classifier comes in.
--- After using CurryStringClassifier.scan the function addTypes only 
--- has to process "Code" tokens and can be sure that there will be no
--- confusion with Comments, Strings or Chars within the program.

addTypes :: Tokens -> [(String,CQualTypeExpr)] -> Tokens
addTypes [] _ = []
addTypes (ModuleHead s:ts)   fts = ModuleHead s : (addTypes ts fts)
addTypes (SmallComment s:ts) fts = SmallComment s : (addTypes ts fts)
addTypes (BigComment s:ts)   fts = BigComment s : (addTypes ts fts)
addTypes (Text s:ts)         fts = Text s : (addTypes ts fts)
addTypes (Letter s:ts)       fts = Letter s : (addTypes ts fts)
addTypes (Code s:ts)         fts = Code newS : newTs
  where
    newS = addTypesCode s newFts fts
    newTs = if null newFts then ts else addTypes ts newFts
    newFts = unknown

--- Within a given  code segment insert all annotations for the contained
--- function and return the new code + the list of functions not yet 
--- inserted (via the logical variable newFts).

addTypesCode :: String -> [(String,CQualTypeExpr)] -> [(String,CQualTypeExpr)]
             -> String
addTypesCode code [] [] = code
addTypesCode code newFts ((f,t):fts)
  | null code = (newFts=:=((f,t):fts)) &> []
  | otherwise 
  = case lhs of 
      [] -> head remainder 
          : addTypesCode (tail remainder) newFts ((f,t):fts)
      ' ':_ -> line ++ addTypesCode remainder newFts ((f,t):fts)
      _ -> if defines f lhs
             then showWidth 78 (ppSig $ normalize t) ++ "\n" ++
                  line ++ addTypesCode remainder newFts fts
             else line ++ addTypesCode remainder newFts ((f,t):fts)

  where
    (line,remainder) = break (=='\n') code
    (lhs,_) = break (=='=') line
    printf = if all (flip elem infixIDs) f then '(':f++")" else f

    ppSig texp = nest 2 $
                   sep [ text printf
                       , align $ doubleColon <+>
                         ppCQualTypeExpr defaultOptions texp]


--- test for functions not typed by the programmer

isUntyped :: CQualTypeExpr -> Bool
isUntyped typeexpr =
  case typeexpr of
    CQualType (CContext []) (CTCons (mod,name))
      -> name == "untyped" && mod == "Prelude"
    _ -> False

------------------------------------------------------------------------------
-- Normalization of type variables in type expressions by enumerating
-- them starting from `(1,"a")` and type variables with singleton
-- occurrences are replaced by `(0,"_")`.

-- The state used during normalization consists of a current number
-- for enumerating type variables, a mapping from old variables
-- to new numbers (which will be expanded during the transformation),
-- and the list of all occurrences of type varables (which will be
-- used to check for single occurrences).
data NormInfo = NormInfo { currNr   :: Int
                         , varMap   :: [(Int,Int)]
                         , allTVars :: [CTVarIName]
                         }

-- The initial normalization state.
initNormInfo :: CQualTypeExpr -> NormInfo
initNormInfo qt = NormInfo 0 [] (allTVarsOfQualType qt)
 where
  allTVarsOfQualType (CQualType (CContext ctxt) t) =
    concatMap (allTVarsTExp . snd) ctxt ++ allTVarsTExp t

  allTVarsTExp (CTVar tv)        = [tv]
  allTVarsTExp (CTCons _)        = []
  allTVarsTExp (CFuncType t1 t2) = allTVarsTExp t1 ++ allTVarsTExp t2
  allTVarsTExp (CTApply t1 t2)   = allTVarsTExp t1 ++ allTVarsTExp t2


-- The type of our actual state monad contains the normalization state.
type TransNorm a = State NormInfo a

-- Auxiliary operation: get a new variable index for a given variable index.
-- Either return the existing index or create a fresh one and update
-- the state.
getVarIndex :: Int -> TransNorm Int
getVarIndex v = do
  ti <- get
  maybe (do let freshnr = currNr ti + 1
            put ti { currNr = freshnr, varMap = (v,freshnr) : varMap ti }
            return freshnr )
        return
        (lookup v (varMap ti))

--- Normalize type expression by rename type variables left-to-right
--- beginning with 0.
normalize :: CQualTypeExpr ->  CQualTypeExpr
normalize qte = evalState (normalizeT qte) (initNormInfo qte)

normalizeT :: CQualTypeExpr -> TransNorm CQualTypeExpr
normalizeT (CQualType (CContext ctxt) t) = do
  ctxt' <- normCtxt ctxt
  t'    <- normTExp t
  return (CQualType (CContext ctxt') t')

normCtxt :: [CConstraint] -> TransNorm [CConstraint]
normCtxt [] = return []
normCtxt ((qf,te) : ctxt) = do
  te'   <- normTExp te
  ctxt' <- normCtxt ctxt
  return ((qf,te') : ctxt')

normTExp :: CTypeExpr -> TransNorm CTypeExpr
normTExp (CTVar tv@(i,_)) = do
  ti <- get
  if length (filter (==tv) (allTVars ti)) <= 1
    then return (CTVar (0,"_"))
    else do ni <- getVarIndex i
            return (toTVar ni)
normTExp (CTCons n) = return (CTCons n) 
normTExp (CFuncType t1 t2) = do
  t1' <- normTExp t1
  t2' <- normTExp t2
  return (CFuncType t1' t2')
normTExp (CTApply t1 t2) = do
  t1' <- normTExp t1
  t2' <- normTExp t2
  return (CTApply t1' t2')

--- Name type variables with a,b,c ... z, t0, t1, ...:
toTVar :: Int -> CTypeExpr
toTVar n | n < 27    = CTVar (n, [chr (96+n)])
         | otherwise = CTVar (n, "t" ++ show (n-27))

------------------------------------------------------------------------------
-- Auxiliaries:

--- a left hand side defines a function named f, if it starts leftmost,
--- and contains f 
defines :: String -> String -> Bool
defines f lhs 
  | null ts = False
  | head lhs == ' ' = False
  | otherwise = elem f ts 
  where
    ts = symbols lhs

--- delimiters between terms on left hand sides
delimiters :: String
delimiters = " ([{,}])"

--- these characters form infix operator names
infixIDs :: String
infixIDs =  "~!@#$%^&*+-=<>?./|\\:"

--- divide a left hand side to a list of symbols contained
--- e.g. symbols "f x [y,z]" = ["f","x","y","z"]
symbols :: String -> [String]
symbols lhs = syms [] lhs
  where
    maybeSym t = if null t then [] else [t]
    syms s [] = maybeSym s
    syms s (x:xs) 
      | elem x delimiters 
      = maybeSym s ++ syms [] (dropWhile (flip elem delimiters) xs)
      | otherwise 
      = syms (s ++ [x]) xs

------------------------------------------------------------------------------
