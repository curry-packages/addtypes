------------------------------------------------------------------
-- A tool to add all those type signatures, you didn't bother to 
-- write while developing the program. 
--
-- @author Bernd Brassel, with changes by Michael Hanus
-- @version November 2016
-- 
-- Possible extensions: Use type synonyms to reduce annotations
------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns #-}

module AddTypes(main,addTypeSignatures) where

import AbstractCurry.Types
import AbstractCurry.Files
import AbstractCurry.Pretty
import AllSolutions
import CurryStringClassifier
import Distribution (stripCurrySuffix)
import FileGoodies
import List
import Pretty
import System (exitWith, system, getArgs)

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
    ["-h"]     -> printUsage
    ["--help"] -> printUsage
    ["-?"]     -> printUsage
    [fname]    -> do
            let progname = stripCurrySuffix fname
            writeWithTypeSignatures progname
            putStrLn $ "Signatures added.\nA backup of the original " ++
                       "file has been written to "++progname++".ORG.curry"
    _          -> printUsage >> exitWith 1

printUsage :: IO ()
printUsage = putStrLn $ unlines
  [ "A tool to add missing type signatures to top-level operations"
  , ""
  , "Usage:"
  , ""
  , "    curry addtypes <Curry program>"
  ]

--- the given file is read three times: a) typed, to get all the necessary 
--- type information b) untyped to find out, which of the types were 
--- specified by the user and c) as a simple string to which the signatures
--- are added. Before adding anything, addtypes will write a backup
--- to <given filename>.ORG.curry

writeWithTypeSignatures :: String -> IO ()
writeWithTypeSignatures progname = do
   system $ "cp -p "++progname++".curry "++progname++".ORG.curry"
   newprog <- addTypeSignatures progname
   writeFile (progname++".curry") newprog

addTypeSignatures :: String -> IO String
addTypeSignatures progname = do
   typedProg <- readCurry progname
   untypedProg <- readUntypedCurry progname
   progLines <- readFile (progname++".curry")
   mbprog <- getOneSolution -- enforce reading of all files before returning
               (\p -> p =:= unscan (addTypes (scan progLines) 
                                             (getTypes typedProg untypedProg)))
   system $ "rm -f "++progname++".acy "++progname++".uacy"
   maybe (error "AddTypes: can't add type signatures") return mbprog


--- retrieve the functions without type signature and their type

getTypes :: CurryProg -> CurryProg -> [(String,CQualTypeExpr)]
getTypes (CurryProg _ _ _ _ _ _ funcDecls1 _)
         (CurryProg _ _ _ _ _ _ funcDecls2 _) 
         = getTypesFuncDecls funcDecls1 funcDecls2
  where
    getTypesFuncDecls [] [] = []
    getTypesFuncDecls (CFunc name _ _ t1 _:fs1) (CFunc _ _ _ t2 _:fs2) 
      | isUntyped t2 = (snd name,t1) : getTypesFuncDecls fs1 fs2
      | otherwise = getTypesFuncDecls fs1 fs2

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
             then pretty 78 (ppSig $ normalize t) ++ "\n" ++
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


--- name type variables with a,b,c ... z, t0, t1, ...

toTVar :: Int -> CTypeExpr
toTVar n | n<26      = CTVar (n,[chr (97+n)])
         | otherwise = CTVar (n,"t"++show (n-26))

--- test for functions not typed by the programmer

isUntyped :: CQualTypeExpr -> Bool
isUntyped typeexpr
   = case typeexpr of
       CQualType (CContext []) (CTCons (mod,name)) ->
                                   name == "untyped" && mod == "Prelude"
       _ -> False

--- normalizing is to rename variables left-right beginning with 0
--- and replace singletons with an "_"
normalize :: CQualTypeExpr -> CQualTypeExpr
normalize t | varNames 0 (tvarsInQualType t newT) = newT  where newT free

--- retrieve all vars contained in a qualified type expression and
--- simultaneously build a new qualified type expression
--- with logical variables for type vars

tvarsInQualType :: CQualTypeExpr -> CQualTypeExpr -> [(Int,CTypeExpr)]
tvarsInQualType (CQualType (CContext cons) t) (CQualType (CContext cons') t') =
  tvarsInContext cons cons' ++ tvars t t'
 where
  tvarsInContext [] [] = []
  tvarsInContext ((qf,te):ctxt) ((qf',te'):ctxt')
    | qf=:=qf' = tvars te te' ++ tvarsInContext ctxt ctxt'

--- retrieve all vars contained in a type expression and simultaneously
--- build a new type expression with logical variables for type vars

tvars :: CTypeExpr -> CTypeExpr -> [(Int,CTypeExpr)]
tvars (CTVar (i,_)) m = [(i,m)]
tvars (CTCons n) (CTCons n') 
  | n=:=n' = []
tvars (CFuncType t1 t2) (CFuncType t1' t2')
  = tvars t1 t1' ++ tvars t2 t2'
tvars (CTApply t1 t2) (CTApply t1' t2')
  = tvars t1 t1' ++ tvars t2 t2'

--- give a list of variables names depending on whether they are singletons
--- or not

varNames :: Eq a => Int -> [(a,CTypeExpr)] -> Bool
varNames _ [] = True
varNames n ((i,v):ivs) 
  | null is =   (v =:= CTVar (0,"_")) &> (varNames n others)
  | otherwise = (giveName (toTVar n) (v:map snd is)) &> (varNames (n+1) others)
  where
    (is,others) = partition (\ (i',_) -> i==i') ivs
    giveName _ [] = True
    giveName name (x:xs) = name=:=x & giveName name xs

--- map on two lists simultaniously. Can't use zip, because the second
--- argument here is a logical variable.

dualMap :: (a -> b -> c) -> [a] -> [b] -> [c]
dualMap _ [] [] = []
dualMap f (x:xs) (y:ys) = f x y:dualMap f xs ys

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
      = syms (s++[x]) xs


