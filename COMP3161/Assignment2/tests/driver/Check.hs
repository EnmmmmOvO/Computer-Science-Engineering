{-# LANGUAGE CPP #-}
-- Haskelly Test Script
-- Written by Liam O'Connor-Davis for comp3161 10s2
-- BSD3
-- Copyright (C) Liam O'Connor-Davis 2010

-- #define NOCOLOR


import Control.Exception

import System.Directory
import Control.Applicative((<$>))
import System.FilePath
import System.Environment
import Data.List
import Control.Monad
import Diff
import System.Process
import System.Exit
import Data.Char

#ifdef NOCOLOR
color v c = c
#else
color v c = v ++ c ++ "\ESC[0m"
#endif

brightWhite = "\ESC[1;97m"
darkWhite = "\ESC[37m"
darkRed = "\ESC[31m"
brightRed = "\ESC[1;91m"
brightGreen = "\ESC[1;92m"
darkYellow = "\ESC[33m"

traverseP :: String -> IO [String]
traverseP path = do
   contents <- getDirectoryContents path
   let sanitizedContents = map (path </>) $ contents \\ ["..","."]
   directories <- filterM doesDirectoryExist sanitizedContents
   files <- filterM doesFileExist sanitizedContents
   if null directories
     then return files
     else do
       traversal <- concat <$> mapM traverseP directories
       return $ traversal ++ files

foreach = flip mapM

showSummary marks = color brightWhite $ if length marks > 0 then "Passed " ++ show (length $ filter (/= 0) marks)
                                                              ++ " out of " ++ show(length marks)
                                                              ++ " tests: " ++ show(((length $ filter (/= 0) marks) * 100) `div` length marks)
                                                              ++ "% Correct. Total of " ++ show (sum marks) ++ " marks."
                                                            else "No tests run."

getSkips skips = concat <$> (foreach skips $ \skip -> map (<.> ".mhs") . map (takeDirectory skip </>) . lines <$> readFile skip)

runTests exe testdir = do
    files <- traverseP $ testdir
    let tests' = filter ((".mhs" ==) . takeExtension) files
    let skips = filter (("Skip" ==) . takeBaseName) files
    tests <- (tests' \\) <$> getSkips skips
    marks <- foreach tests $ (\test -> do
      (expect_fail, flags) <- getFlags (test `replaceFileName` "Flag")
      mark <- getMarks (test `replaceFileName` "Marks")
      putStr $ color brightWhite ("Running test: ") ++ color darkWhite (makeRelative testdir test) ++ color brightWhite (" (worth " ++ show mark ++ ") :-  ")
      (exit, out, err) <- readCreateProcessWithExitCode (shell (unwords $ exe : (flags ++ ["--no-colour", test]))) ""
      let check = do r1 <- doCheck ".out" "Stdout" test out
                     r2 <- doCheck ".err" "Stderr" test err
                     return $ r1 * r2 * mark
      case exit of
        ExitFailure i -> if expect_fail then check
                         else do putStrLn $ color darkRed ("Executable returned non-zero exit code(" ++ show i ++ ").")
                                 dumpOutput err out
        ExitSuccess -> if not expect_fail then check
                       else do putStrLn $ color darkRed ("Expected program failure, but it unexpectedly succeeded.")
                               dumpOutput err out)
    putStrLn $ showSummary marks
  where
    dumpOutput err out = do
      putStrLn $ color darkRed ("Stderr was:")
      putStrLn err
      putStrLn $ color darkRed ("Stdout was:")
      putStrLn out
      return 0
    doCheck ext name test out = do
      v <- doesFileExist (test `replaceExtension` ext)
      if v
        then do
          diff <- getDiff (filter (not . all isSpace) $ lines out) <$> filter (not . all isSpace) . lines <$> readFile (test `replaceExtension` ".out")
          if all (== B) $ map fst diff
            then putStrLn (color brightGreen $ name ++ " Check Passed!") >> return 1
            else do putStrLn $ (color brightRed $ name ++ " Check Failed") ++ ":\n" ++ showDiff diff; return 0
        else if (not $ all isSpace out)
          then do
            putStrLn $ color darkYellow $ "No " ++ ext ++ " file found. Printing output..."
            putStr out
            return 1
          else return 1

getFlags filename = do
  v <- doesFileExist filename
  if v then do
         str <- lines <$> readFile filename
         return ("expect-fail" `elem` str, delete "expect-fail" str)
       else return (False, [])

getMarks filename = let readInteger s = case reads s of
                                            [(a,b)] -> a
                                            _       -> 1
                     in do v <- doesFileExist filename
                           if v then  readInteger <$> readFile filename
                                else return 1

main = do
  cd <- getCurrentDirectory
  v <- getArgs
  when (v == [ "--help" ]) $ do
     putStrLn $ "Liam's Haskelly Test Runner v0.1. \n" ++
                "This program is usually accompanied by a runner shell script.\n" ++
                "  Usage: ./run_tests.sh [--no-color] [program_to_test] [test_folder_location]\n\n" ++
                "If no shell script is available, it can be run easily via runhaskell:\n" ++
                "  Usage: runhaskell -i./tests/driver -cpp [-DNOCOLOR] ./tests/driver/Check.hs [program_to_test] [test_folder_location]"
     exitSuccess
  let (dir, exe) = case filter (/= "") v of
                     [ filename ] -> (cd </> "tests", filename)
                     [ filename, tests ] -> (tests, filename)
                     [] -> (cd </> "tests", cd </> "dist" </> "build" </> "minhs-1" </> "minhs-1")
                     _ -> error (show v)
  de <- doesDirectoryExist $ cd </> "tests"
  --fe <- doesFileExist $ exe
  --when (not fe) $ error $ "I cannot find an executable. I tried:" ++ exe
  when (not de) $ error "I cannot find a `tests' directory. Exiting"
  runTests exe dir

showDiff :: [(DI,String)] -> String
showDiff diff = unlines $ map (\(a,b) -> color (colorDI a) (showDI a ++ b )) diff
 where showDI F = "+"
       showDI S = "-"
       showDI B = " "
       colorDI F = darkRed
       colorDI S = darkRed
       colorDI B = darkWhite
