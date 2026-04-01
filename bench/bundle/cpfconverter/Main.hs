module Main(main) where

import System.Environment -- for getArgs
import System.IO -- for file reading
import CPF_2_to_3

main = getArgs >>= parse False

info = putStrLn "usage: cpf2_to_3_phase_1 [--termIndex] [cpf2.xml | -]"

parse _ [] = info
parse _ ("--termIndex" : args) = parse True args
parse ti ([fname]) = if fname == "-" then interact (cpf_2_to_3_phase_1 ti) else do
      inp <- readFile fname
      putStrLn (cpf_2_to_3_phase_1 ti inp)
parse _ _ = info
