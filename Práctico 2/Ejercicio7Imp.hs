{-# OPTIONS_GHC -fno-warn-tabs #-}

-- a) No se modifican, solamente se agrega ∆ en la ejecución antes de la respectiva M

-- b)

--      ----------------------------------------------------------------- def.fun.
--       (Δ, M) ▷ def f(𝑥̄) returns x { p } ▷ (Δ <+ (f, 𝑥̄, x, p), M) 

--       ē -M-> v̄          Δ, (x̄, v̄) ▷ p ▷ Δ',M'                    f -Δ-> (x̄,x,p)
--      ------------------------------------------- inv.fun.         #x̄ = #ē
--       (Δ, M) ▷ f(ē) on r ▷ Δ, (M <+ (r, M'x))                    nub(r:x̄) = r:x̄

data Prog =  AsigMult [X] [Exp]
            | Local [X] Prog
            | Sec Prog Prog
            | Case X [Branch]
            | While X [Branch]
            | Def F [X] X Prog -- def f(𝑥̄) returns x { p } 
            | App F [Exp] X -- f(ē) on r

data Exp = Cons C [Exp]
        |  Var X

type Branch = (C, [X], Prog)

type X = String
type C = String
type F = String

data Val = ConsV C [Val]
        |   Null
        deriving (Show)

type Mem = [(X,Val)]

type Env = [(F,[X],X,Prog)] -- environment

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


-- funciones para operar sobre el environment. (ver foldr)
busquedaEnv :: Env -> F -> ([X],X,Prog)
busquedaEnv ((f,xs,x,p):es) f'
    | f == f' = (xs,x,p)
    | otherwise = busquedaEnv es f'

actualizacionEnv :: Env -> (F,[X],X,Prog) -> Env
actualizacionEnv [] f = [(f)]
actualizacionEnv ((f,xs,x,p):es) (f',xs',x',p')
    | f == f' = (f',xs',x',p'):es
    |otherwise = (f,xs,x,p): (actualizacionEnv es (f',xs',x',p'))

-- evalucación de expresiones (ver let)
eval :: Exp -> Mem -> Val
eval (Var x) m = (busqueda m x)
eval (Cons c es) m = ConsV c (evalAux es m)

evalAux :: [Exp] -> Mem -> [Val]
evalAux [] m = []
evalAux (e:es) m = (eval e m) : (evalAux es m)

-- ejecución de programas (ver let)
exec :: (Env, Mem) -> Prog -> (Env, Mem)
exec (e,m) (AsigMult xs es) = (e,actualizacion m (zip xs (evalAux es m)))
exec (e,m) (Local xs p) =
    let (e',m') = exec (e, altas xs m) p
    in  (e',bajas xs m')
exec (e,m) (Sec p1 p2) = 
    let (e',m') = exec (e,m) p1
    in exec (e',m') p2 
exec (e,m) (Case x bs) = case eval (Var x) m of
    (ConsV c vs) -> case (buscarRama c bs) of 
        Just (xs,p) -> exec (e,m) (Local xs (Sec (AsigMult xs (promoteAll vs)) p))
exec (e,m) (While x bs) = case eval (Var x) m of
    (ConsV c vs) -> case (buscarRama c bs) of
        Just (xs,p) -> 
            let (e',m') = exec (e,m) (Local xs (Sec (AsigMult xs (promoteAll vs)) p))
            in exec (e',m') (While x bs)
        Nothing -> (e,m)
exec (e,m) (Def f xs x p) = (actualizacionEnv e (f,xs,x,p),m)
exec (e,m) (App f es r) = case busquedaEnv e f of
    (xs,x,p) ->
        let (e',m') = exec (e,(zip xs (evalAux es m))) p
        in (e, actualizacion m [(r,busqueda m' x)])

    
buscarRama :: C -> [Branch] -> Maybe ([X], Prog)
buscarRama c []= Nothing
buscarRama c ((c', xs, p):bs)
    | c == c' = Just (xs,p)
    | otherwise = buscarRama c bs

promote :: Val -> Exp
promote (ConsV c vs) = Cons c (map promote vs)

promoteAll :: [Val] -> [Exp]
promoteAll vs = map promote vs

-- con let:
-- exec m (Local xs p) = let m1 = altas m xs in 
--                          let m2 = exec m1 p in
--                              bajas m2 xs

-- ANYEVEN
anyEven :: Prog
anyEven = Sec
    (Def "not" ["b"] "r" (Case "b" [
        ("True", [], AsigMult ["r"] [Cons "False" []]),
        ("False", [], AsigMult ["r"] [Cons "True" []])
        ])
    )
    (Sec 
    (Def "par" ["n"] "r" (
        Local ["n'", "ac"] (
        Sec
            (Sec
                (AsigMult ["n'", "ac"] [Var "n", Cons "True" []])
                (While "n'" [
                    ("S", ["x"], Sec (App "not" [Var "ac"] "r")
                                     (AsigMult ["n'", "ac"] [Var "x", Var "r"]))
                ])
            )
            (AsigMult ["r"] [Var "ac"])
        )
    ))
    (
        Local ["parX", "parY", "parZ"] (
            Sec
                (App "par" [Var "x"] "parX")
                (
                    Sec
                    (App "par" [Var "y"] "parY")
                    (
                        Sec
                        (App "par" [Var "z"] "parZ")
                        (
                            Case "parX" [
                                ("True", [], AsigMult ["res"] [Cons "True" []]),
                                ("False", [], Case "parY" [
                                    ("True", [], AsigMult ["res"] [Cons "True" []]),
                                    ("False", [], Case "parZ" [
                                        ("True", [], AsigMult ["res"] [Cons "True" []]),
                                        ("False", [], AsigMult ["res"] [Cons "False" []])
                                    ])
                                ])
                            ]
                        )
                    )
                )
        )
    ))


-- TESTS
memTest1 :: Mem
memTest1 = [("x", ConsV "Z" []), ("y", ConsV "Z" []), ("z", ConsV "Z" [])]
anyEvenTrueTest :: Mem
anyEvenTrueTest = snd (exec ([], memTest1) anyEven)

memTest2 :: Mem
memTest2 = [("x", ConsV "S" [ConsV "Z" []]), ("y", ConsV "S" [ConsV "Z" []]), ("z", ConsV "S" [ConsV "Z" []])]
anyEvenFalseTest :: Mem
anyEvenFalseTest = snd (exec ([], memTest2) anyEven)

memTest3 :: Mem
memTest3 = [("x", ConsV "S" [ConsV "Z" []]), ("y", ConsV "Z" []), ("z", ConsV "Z" [])]
anyEvenTrueTest2 :: Mem
anyEvenTrueTest2 = snd (exec ([], memTest3) anyEven)