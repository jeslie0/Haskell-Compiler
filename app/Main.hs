facProg :: Int -> Prog
facProg n = Seqn [ Assign 'A' (Val 1)
               , Assign 'B' (Val n)
               , While (Var 'B') (Seqn [ Assign 'A' (App Mul (Var 'A') (Var 'B'))
                                       , Assign 'B' (App Sub (Var 'B') (Val 1))
                                       ])
               ]

sumProg :: Int -> Prog
sumProg n = Seqn [ Assign 'A' (Val 1)
               , Assign 'B' (Val n)
               , While (App Sub (Var 'B') (Val 1)) (Seqn [ Assign 'A' (App Add (Var 'A') (Var 'B'))
                                       , Assign 'B' (App Sub (Var 'B') (Val 1))
                                       ])
               ]
testProg :: Prog
testProg = Seqn [ While (Val 1) (While (Val 2) (While (Val 3) (Assign 'a' (Val 4)))),
                  While (Val 1) (While (Val 2) (While (Val 3) (Assign 'a' (Val 4))))
                ]

testProg1 :: Prog
testProg1 = Seqn [ While (Val 1) (If (Val 1) (Assign 'a' (Val 1)) (While (Val 6) (Assign 'a' (Val 4)))),
                   While (Val 2) (Assign 'b' (Val 5))
                ]

precompExp' :: Expr -> Code -> Code
precompExp' (Val n) code = PUSH n : code
precompExp' (Var c) code = PUSHV c : code
precompExp' (App op exp1 exp2) code = precompExp' exp1 (precompExp' exp2 (DO op : code))

precompExp :: Expr -> Code
precompExp exp = precompExp' exp []

comp' :: Prog -> State Int Code
comp' (Assign nom exp) =
  return $ precompExp' exp [POP nom]
comp' (Seqn []) = return []
comp' (Seqn (x:xs)) = do
  y <- comp' x
  ys <- comp' (Seqn xs)
  return $ y ++ ys
comp' (If exp prog1 prog2) = do
  n <- fresh
  m <- fresh
  pr1 <- comp' prog1
  pr2 <- comp' prog2
  return $
    precompExp' exp $
    (JUMPZ n : pr1) ++ (JUMP m : LABEL n : pr2) ++ [LABEL m]
comp' (While exp prog) = do
  n <- fresh
  m <- fresh
  pr <- comp' prog
  return $
    LABEL n : precompExp' exp (
    (JUMPZ m : pr) ++ [JUMP n, LABEL m])

comp :: Prog -> Code
comp prog = evalState (comp' prog) 0

comp :: Prog -> Code
comp prog = evalState (comp' prog) 0

type CodeZipper = (Code, Code)
goForward :: CodeZipper -> CodeZipper
goForward (x:xs, bs) = (xs, x:bs)

goBack :: CodeZipper -> CodeZipper
goBack (xs, b:bs) = (b:xs, bs)

codeZipToCode :: CodeZipper -> Code
codeZipToCode (xs, []) = xs
codeZipToCode (xs, a:as) = codeZipToCode (a:xs, as)

codeToCodeZip :: Code -> CodeZipper
codeToCodeZip code = (code,[])

findKey :: (Eq k) => k -> [(k,v)] -> v
findKey key = snd . head . filter (\(k,v) -> key == k)

updateKey :: (Eq k) => k -> v -> [(k,v)] -> [(k,v)]
updateKey k v dict = (k,v):filter (\(a,_) -> a /= k) dict

exec' :: CodeZipper -> Mem -> Stack -> Mem
exec' ([],_) mem _ = mem

exec' zip@(PUSH n:xs, bs) mem stack = exec' (goForward zip) mem (n:stack)
exec' zip@(PUSHV char:xs, bs) mem stack = exec' (goForward zip) mem (findKey char mem:stack)

-- exec' zip@(POP char:xs, bs) mem [] = [(char, 838383)] ++ mem
exec' zip@(POP char:xs, bs) mem (y:ys) = exec' (goForward zip) (updateKey char y mem) ys

-- exec' zip@(DO op:xs, bs) mem [] = [('X',101010)]
-- exec' zip@(DO op:xs, bs) mem [y1] = [('Y', 2999)]
exec' zip@(DO op:xs, bs) mem (y1:y2:ys) = exec' (goForward zip) mem (eval op y2 y1:ys)

exec' zip@(JUMP label:xs, bs) mem stack = exec' newZip mem stack
  where
    newZip = twist $ break (\a -> a == LABEL label) (codeZipToCode zip)

-- exec' zip@(JUMPZ label:xs, bs) mem [] = [('Z', 1010101001)] ++ mem
exec' zip@(JUMPZ label:xs, bs) mem (y:ys)
  | y == 0    = exec' (JUMP label:xs, bs) mem ys
  | otherwise = exec' (goForward zip) mem ys
exec' zip@(LABEL label:xs, bs) mem stack = exec' (goForward zip) mem stack



exec :: Code -> Mem
exec code = exec' (codeToCodeZip code) [] []

compT' :: Prog -> WriterT Code (State Int) ()
compT' (Assign name exp) =
  tell $ precompExp' exp [POP name]
compT' (If exp prog1 prog2) = do
  n <- lift fresh
  m <- lift fresh
  pr1 <- lift . execWriterT $ compT' prog1
  pr2 <- lift . execWriterT $ compT' prog2
  tell $ precompExp' exp $ (JUMPZ n : pr1) ++ (JUMP m : LABEL n : pr2) ++ [LABEL m]
compT' (While exp prog) = do
  n <- lift fresh
  m <- lift fresh
  pr <- lift (execWriterT $ compT' prog)
  tell $ LABEL n : precompExp' exp ((JUMPZ m : pr) ++ [JUMP n, LABEL m])
compT' (Seqn []) =
  tell []
compT' (Seqn (x:xs)) = do
  y <- lift $ execWriterT (compT' x)
  ys <- lift $ execWriterT (compT' (Seqn xs))
  tell $ y ++ ys

compT :: Prog -> Code
compT prog = (evalState $ execWriterT (compT' prog)) 0
