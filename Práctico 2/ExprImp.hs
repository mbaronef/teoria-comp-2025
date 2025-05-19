{-# OPTIONS_GHC -fno-warn-tabs #-}

data Prog =  AsigMult [X] [Exp]
            | Local [X] Prog
            | Sec Prog Prog
            | Case X [Branch]
            | While X [Branch]

data Exp = Cons C [Exp]
        |  Var X

type Branch = (C, [X], Prog)

type X = String
type C = String

data Val = ConsV C [Val]
        |   Null
        deriving (Show)

type Mem = [(X,Val)]

-- funciones para operar sobre la memoria. (ver foldr)
busqueda :: Mem -> X -> Val
busqueda ((y,v):ms) x
    | x == y = v
    | otherwise = busqueda ms x

actualizacion :: Mem -> [(X,Val)] -> Mem
actualizacion m [] = m
actualizacion m (x:xs) = actualizacion (actualizacionUno m x) xs

actualizacionUno :: Mem -> (X,Val) -> Mem
actualizacionUno [] (x,v) = [(x,v)]
actualizacionUno ((y,v):ms) (x,v')
    |  x == y = (x,v'):ms
    |  otherwise = (y,v) : (actualizacionUno ms (x,v'))

altas :: [X] -> Mem -> Mem
altas [] m = m
altas (x:xs) m = (x, Null):(altas xs m)

bajas ::  [X] -> Mem -> Mem
bajas [] m = m
bajas (x:xs) m = bajas xs (bajasAux x m)

bajasAux :: X -> Mem -> Mem
bajasAux x [] = []
bajasAux x ((y,v):ms)
    | x == y = ms
    | otherwise = (y,v):(bajasAux x ms)

--con foldr
--bajas xs m = foldr bajasAux m xs
  --  where
    --    bajasAux :: X -> Mem -> Mem
      --  bajasAux x [] = []
        --bajasAux x ((y,v):ms) 
          --  |   x == y = ms
            -- |   otherwise = (y,v):(bajasAux x ms)

-- evalucación de expresiones (ver let)
eval :: Exp -> Mem -> Val
eval (Var x) m = (busqueda m x)
eval (Cons c es) m = ConsV c (evalAux es m)

evalAux :: [Exp] -> Mem -> [Val]
evalAux [] m = []
evalAux (e:es) m = (eval e m) : (evalAux es m)

-- ejecución de programas (ver let)
exec :: Mem -> Prog -> Mem
exec m (AsigMult xs es) = actualizacion m (zip xs (evalAux es m))
exec m (Local xs p) = bajas xs (exec (altas xs m) p)
exec m (Sec p1 p2) = exec (exec m p1) p2 
exec m (Case x bs) = case eval (Var x) m of
    (ConsV c vs) -> case (buscarRama c bs) of 
        Just (xs,p) -> exec m (Local xs (Sec (AsigMult xs (promoteAll vs)) p))
exec m (While x bs) = case eval (Var x) m of
    (ConsV c vs) -> case (buscarRama c bs) of
        Just (xs,p) -> exec (exec m (Local xs (Sec (AsigMult xs (promoteAll vs)) p))) (While x bs)
        Nothing -> m
    
buscarRama :: C -> [Branch] -> Maybe ([X], Prog)
buscarRama c []= Nothing
buscarRama c ((c', xs, p):bs)
    | c == c' = Just (xs,p)
    | otherwise = buscarRama c bs

promote :: Val -> Exp
promote (ConsV c vs) = Cons c (map promote vs)

promoteAll :: [Val] -> [Exp]
promoteAll vs = map promote vs

-- ej con let:
-- exec m (Local xs p) = let m1 = altas m xs in 
--                          let m2 = exec m1 p in
--                              bajas m2 xs

-- Programas en IMP
notImp :: Prog
notImp = Case "ac" [
    ("True", [], (AsigMult ["res"] [Cons "False" []])),
    ("False", [], (AsigMult ["res"] [Cons "True" []]))  
    ]

parImp :: Prog
parImp = Local ["n'", "ac"] (
    Sec
        (Sec
            (AsigMult ["n'", "ac"] [Var "n", Cons "True" []])
            (While "n'" [
                ("S", ["x"], Sec notImp (AsigMult ["n'", "ac"] [Var "x", Var "res"]))
            ])
        )
        (AsigMult ["res"] [Var "ac"])
    )

sumaImp :: Prog 
sumaImp = Local ["ac", "n'"] (
    Sec 
        (   
            Sec
            (AsigMult ["ac", "n'"] [Var "m", Var "n"])
            (While "n'" [
                ("S", ["x"], AsigMult ["ac", "n'"] [Cons "S" [Var "ac"], Var "x"])
            ])
        )
        (AsigMult ["res"] [Var "ac"])
    )

largoImp :: Prog
largoImp = Local ["ac", "l'"] (
    Sec
        (
            Sec 
            (AsigMult ["ac", "l'"] [Cons "Z" [], Var "l"])
            (While "l'" [
               ( ":", ["x", "xs"], AsigMult ["ac", "l'"] [Cons "S" [Var "ac"], Var "xs"])
            ])
        )
        (AsigMult ["res"] [Var "ac"])
    )

igualdadNImp :: Prog
igualdadNImp = Local ["m'", "n'"] (
    Sec
    (AsigMult ["m'", "n'", "res"] [Var "m", Var "n", Cons "True" []])
    (
        Sec
        (
            While "m'" [
                ("S", ["x"], Case "n'" [
                    ("S", ["y"], AsigMult ["m'","n'"] [Var "x", Var "y"]),
                    ("Z", [], AsigMult ["res", "m'"] [Cons "False" [], Cons "Z" []])
                ])
            ]
        )
        (
            Case "n'" [
            ("Z", [], AsigMult ["res"] [Var "res"]),
            ("S", ["x"], AsigMult ["res"] [Cons "False" []])
            ]
        )
    )
    )

concatImp :: Prog
concatImp = Local ["l1'", "l2'", "inv"](
    Sec
    (AsigMult ["l1'", "l2'", "inv", "res"] [Var "l1", Var "l2", Cons "[]" [], Cons "[]" []])
    (
        Sec
        (
            While "l1'" [
                (":", ["x", "xs"], AsigMult ["l1'", "inv"] [Var "xs", Cons ":" [Var "x", Var "inv"]])
            ]
        )
        (
            Sec
            (
                While "l2'" [
                (":", ["y", "ys"], AsigMult ["l2'", "inv"] [Var "ys", Cons ":" [Var "y", Var "inv"]])
                ]
            )
            (
                While "inv" [
                (":", ["z", "zs"], AsigMult ["inv", "res"] [Var "zs", Cons ":" [Var "z", Var "res"]])
                ]
            )
        )
    )
    )

-- TESTS
notTest :: Mem
notTest = exec [("ac", ConsV "True" [])] notImp

parTrueTest :: Mem
parTrueTest = exec [("n", ConsV "Z" []) ] parImp

parFalseTest :: Mem
parFalseTest = exec [("n", ConsV "S" [ConsV "Z" []]), ("res", ConsV "False" [])] parImp

sumaUnoTest :: Mem
sumaUnoTest = exec [("m", ConsV "Z" []), ("n", ConsV "S" [ConsV "Z" []])] sumaImp

sumaDosTest :: Mem
sumaDosTest = exec [("m", ConsV "S" [ConsV "Z" []]), ("n", ConsV "S" [ConsV "Z" []])] sumaImp

largoCeroTest :: Mem
largoCeroTest = exec [("l", ConsV "[]" [])] largoImp

largoUnoTest :: Mem
largoUnoTest = exec [("l", ConsV ":" [ConsV "Z" [], ConsV "[]" []])] largoImp

largoDosTest :: Mem
largoDosTest = exec [("l", ConsV ":" [ConsV "Z" [], ConsV ":" [ConsV "Z" [] ,ConsV "[]" []]])] largoImp

igualdadTrueTest :: Mem
igualdadTrueTest = exec [("m", ConsV "S" [ConsV "Z" []]), ("n", ConsV "S" [ConsV "Z" []])] igualdadNImp

igualdadFalseTest1 :: Mem
igualdadFalseTest1 = exec [("m", ConsV "Z" []), ("n", ConsV "S" [ConsV "Z" []])] igualdadNImp

igualdadFalseTest2 :: Mem
igualdadFalseTest2 = exec [("n", ConsV "Z" []), ("m", ConsV "S" [ConsV "Z" []])] igualdadNImp

concatVaciasTest :: Mem
concatVaciasTest = exec [("l1", ConsV "[]" []), ("l2", ConsV "[]" [])] concatImp

concatDerVaciaTest :: Mem -- tiene que dar [Z]
concatDerVaciaTest = exec [("l1", ConsV ":" [ConsV "Z" [], ConsV "[]" []]),("l2", ConsV "[]" [])] concatImp

concatNoVaciasTest :: Mem -- tiene que dar [Z,S(Z)]
concatNoVaciasTest = exec [("l1", ConsV ":" [ConsV "Z" [], ConsV "[]" []]),("l2", ConsV ":" [ConsV "S" [ConsV "Z" []], ConsV "[]" []])] concatImp

-- ÁRBOL - clase 7/5 11:55hs