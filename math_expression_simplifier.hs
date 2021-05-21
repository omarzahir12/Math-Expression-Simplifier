{- Assignment
 - Name: Mohammad Omar Zahir
 -}
module Assign where

macid :: String
macid = "zahirm1"

data MathExpr a = X
                | Coef a
                | Sum (MathExpr a) (MathExpr a)
                | Prod (MathExpr a) (MathExpr a)
                | Quot (MathExpr a) (MathExpr a)
                | Exp (MathExpr a)
                | Log (MathExpr a)
                deriving (Eq,Show,Read)

{- -----------------------------------------------------------------
 - value
 - -----------------------------------------------------------------
 - Description: Evaluates the value of a type MathExpr into type 
   Floating given a MathExpr and Floating as input
 -}

value :: (Floating a, Eq a) => MathExpr a -> a -> a
value X n = n
value (Coef a) n = a
value (Sum u v) n = (value u n) + (value v n)
value (Prod u v) n = (value u n) * (value v n)
value (Quot u v) n = (value u n) / (value v n)
value (Exp u) n = exp (value u n)
value (Log u) n = log (value u n)

{- -----------------------------------------------------------------
 - simp
 - -----------------------------------------------------------------
 - Description: Takes input of type MathExpr and returns a simplified
   version of the MathExpr that follows the following criteria:
    0+u=u
    u+0=u.
    0*u=0
    u*0=0
    1*u=u
    u*1=u
    u/1=u
    exp(0)=1
    log(1)=0
    
    Similarily, if any further simplifcation is equal to the prior 
    simplification than just the expression will be returned 
 -}

simp :: (Floating a, Eq a) => MathExpr a -> MathExpr a
simp X = X
simp (Coef a) = Coef a
--Sum
simp (Sum (Coef 0.0) u) = simp u
simp (Sum u (Coef 0.0)) = simp u
simp (Sum u v)
    | ((u' == u) && (v' == v)) = (Sum u v)
    | otherwise = simp (Sum u' v')
    where 
        u' = simp u
        v' = simp v
--Prod
simp (Prod (Coef 0.0) u) = Coef 0.0
simp (Prod u (Coef 0.0)) = Coef 0.0 
simp (Prod (Coef 1) u) = simp u
simp (Prod u (Coef 1)) = simp u
simp (Prod u v)
    | ((u' == u) && (v' == v)) = (Prod u v)
    | otherwise = simp (Prod u' v')
    where 
        u' = simp u
        v' = simp v
--Quot
simp (Quot u (Coef 1)) = simp u
simp (Quot u v)
    | ((u' == u) && (v' == v)) = (Quot u v)
    | otherwise = simp (Quot u' v')
    where 
        u' = simp u
        v' = simp v
--Exp
simp (Exp (Coef 0.0)) = Coef 1
simp (Exp u)
    | (u' == u) = (Exp u)
    | otherwise = simp (Exp u')
    where 
        u' = simp u
--Log
simp (Log (Coef 1)) = Coef 0.0
simp (Log u)
    | (u' == u) = (Log u)
    | otherwise = simp (Log u')
    where 
        u' = simp u

{- -----------------------------------------------------------------
 - diff
 - -----------------------------------------------------------------
 - Description: Takes a MathExpr as input and returns a MathExpr that 
   applies the following derivative rules on the expression
   Variable Rule
   Constant Rule
   Sum Rule
   Product Rule
   Quotient Rule
   Exponentiation Rule
   Logarithm Rule
 -}     

diff :: (Floating a, Eq a) => MathExpr a -> MathExpr a
diff X = Coef 1
diff (Coef a) = Coef 0.0
diff (Sum u v) = simp (Sum (diff (u)) (diff (v)))
diff (Prod u v) = simp (Sum (Prod (diff (u)) (v)) (Prod (diff (v)) (u)))
diff (Quot u v) = simp (Quot (Sum (Prod (diff (u)) (v)) (Prod (Coef (-1)) (Prod (diff (v)) (u)))) (Prod (v) (v)))
diff (Exp u) = simp (Prod (Exp (u)) (diff (u)))
diff (Log u) = simp (Quot (diff (u)) (u))

{- -----------------------------------------------------------------
 - readDiffWrite
 - -----------------------------------------------------------------
 - Description: This function takes two file paths as input, from which
   one has the MathExpr written in text. The function reads the MathExpr
   by converting it and then applies the diff, and returns the output to
   second input file that was given
 -}

readDiffWrite :: FilePath -> FilePath -> IO ()
readDiffWrite f g = do
    u <- readFile f 
    let v = read u :: MathExpr Double
    writeFile g (show (diff v))

{- -----------------------------------------------------------------
 - Test Cases
 - -----------------------------------------------------------------
 -
 - -----------------------------------------------------------------
 - - Function: value
 - - Test Case Number: 1
 - - Input: (Prod (X) (Sum (Coef 5) X))  2
 - - Expected Output: 14.0
 - - Acutal Output: 14.0
 - -----------------------------------------------------------------
 - - Function: value
 - - Test Case Number: 2
 - - Input: value (Exp (Log X)) 1
 - - Expected Output: 1.0
 - - Acutal Output: 1.0
 - -----------------------------------------------------------------
 - - Function: value
 - - Test Case Number: 3
 - - Input: (Quot (1) (Prod (Coef 5) X)) 2
 - - Expected Output: 0.1
 - - Acutal Output: 0.1
 - -----------------------------------------------------------------
 - - Function: simp
 - - Test Case Number: 1 
 - - Input: (Prod (Coef 0) X)
 - - Expected Output: Coef 0.0
 - - Acutal Output: Coef 0.0
 - -----------------------------------------------------------------
 --  Function: simp
 - - Test Case Number: 2 
 - - Input: (Log (Exp (Coef 0)))
 - - Expected Output: Coef 0.0
 - - Acutal Output: Coef 0.0
 - -----------------------------------------------------------------
 --  Function: simp
 - - Test Case Number: 3 
 - - Input: (Quot (Prod (Coef 1) X) (Coef 1))
 - - Expected Output: X
 - - Acutal Output: X
 - -----------------------------------------------------------------
 --  Function: diff
 - - Test Case Number: 1
 - - Input: Sum (Coef 1) (X)
 - - Expected Output: Coef 1.0
 - - Acutal Output: Coef 1.0
 - -----------------------------------------------------------------
 --  Function: diff
 - - Test Case Number: 2 
 - - Input: Prod (Coef 2) (Quot (Coef 1) X) 
 - - Expected Output: Prod (Quot (Coef (-1.0)) (Prod X X)) (Coef 2.0)
 - - Acutal Output: Prod (Quot (Coef (-1.0)) (Prod X X)) (Coef 2.0)
 - -----------------------------------------------------------------
 --  Function: diff
 - - Test Case Number: 3
 - - Input: Sum (Coef 1) (Prod (X) (Exp X))
 - - Expected Output: Sum (Exp X) (Prod (Exp X) X)
 - - Acutal Output: Sum (Exp X) (Prod (Exp X) X)
 - -----------------------------------------------------------------
 --  Function: readDiffWrite
 - - Test Case Number: 1
 - - Input File Contents: Prod X X
 - - Expected Output File COntents: Sum X X
 - - Acutal Output File Contents: Sum X X
 - -----------------------------------------------------------------
 --  Function: readDiffWrite
 - - Test Case Number: 2
 - - Input File Contents: Prod (Coef 3) (Quot (Coef 1) X)
 - - Expected Output File Contents: Prod (Quot (Coef (-1.0)) (Prod X X)) (Coef 3.0)
 - - Acutal Output File Contents: Prod (Quot (Coef (-1.0)) (Prod X X)) (Coef 3.0)
 - -----------------------------------------------------------------
 -- - Function: readDiffWrite
 - - Test Case Number: 3
 - - Input File Contents: Sum (Coef 1) (Prod (Coef 5) (Exp X))
 - - Expected Output File Contents: Prod (Exp X) (Coef 5.0)
 - - Acutal Output File Contents: Prod (Exp X) (Coef 5.0)
 - -----------------------------------------------------------------
 - 
 -}

