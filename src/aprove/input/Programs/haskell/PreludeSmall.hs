module Prelude (
	error, undefined
  ) where

terminator = terminator

stopEval :: Bool -> a
stopEval False = stopEval False

error :: a
error = stopEval True

undefined :: a
undefined = stopEval True

negate = negate