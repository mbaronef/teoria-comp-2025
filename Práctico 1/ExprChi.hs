{-# OPTIONS_GHC -fno-warn-tabs #-}

data Exp = Var X
        |   Cons K [Exp]
        |   Lam X Exp
        |   App Exp Exp
        |   Case Exp [Branch]
        |   Rec X Exp
        |   If Exp Exp Exp -- ejercicio 9 || BNF: e :: = if e then e else e
        deriving (Show, Eq)

type X = String
type K = String
type Branch = (K, ([X], Exp))

data V = ConsV K [V]
    |    LamV X Exp
    deriving (Show, Eq)

data W = ConsW K [Exp]
    |   LamW X Exp


-- Sustituciones
type S = [(X,Exp)] --sustitución

busqueda :: X -> S -> Exp
busqueda x [] = Var x
busqueda x ((y,e):ys)
    | x == y = e
    | otherwise = busqueda x ys

bajas :: [X] -> S -> S
bajas [] s = s
bajas (x:xs) s = bajas xs (bajasAux x s)

bajasAux :: X -> S -> S
bajasAux x [] = []
bajasAux x ((y,e):ys)
    |   x == y = bajasAux x ys
    |   otherwise = (y,e) : (bajasAux x ys)

efecto :: Exp -> S -> Exp
efecto (Var x) s = busqueda x s
efecto (Cons k es) s = Cons k (efectoConsAux es s) -- Cons k (map (flip efecto s) es) 
efecto (Lam x e) s = Lam x (efecto e (bajas [x] s))
efecto (App e e') s = App (efecto e s) (efecto e' s)
efecto (Case e bs) s = Case (efecto e s) (efectoCaseAux bs s) 
efecto (Rec x e) s = Rec x (efecto e (bajas [x] s))

efectoConsAux :: [Exp] -> S -> [Exp]
efectoConsAux [] s = []
efectoConsAux (e:es) s = (efecto e s) : (efectoConsAux es s)

efectoCaseAux :: [Branch] -> S -> [Branch]
efectoCaseAux [] s = []
efectoCaseAux ((k,(xs,e)):bs) s = (k,(xs, efecto e (bajas xs s))) : (efectoCaseAux bs s)


-- Evaluación debil
weak :: Exp -> W
weak (Cons k es) = ConsW k es
weak (Lam x e) = LamW x e
weak (App e e') = case weak e of
    LamW x e'' -> weak (efecto e'' [(x,e')])
    ConsW k es -> ConsW k (es ++ [e']) 
weak (Case e bs) = case weak e of
    ConsW k es -> case (buscarRama bs k) of
        (xs, e') -> weak (efecto e' (armarListaSustitucion xs es))
weak (Rec x e) = weak (efecto e [(x,Rec x e)])
weak (If e1 e2 e3) = case (weak e1) of -- Ejercicio 9
    ConsW "True" [] -> weak e2
    ConsW "False" [] -> weak e3

buscarRama :: [Branch] -> K -> ([X],Exp) -- no hay vacío porque se asume que siempre se encuentra
buscarRama ((k,(xs,e)):bs) k'
    | k == k' = (xs, e)
    | otherwise = buscarRama bs k'

armarListaSustitucion :: [X] -> [Exp] -> S -- se asume #[X] = #[Exp]
armarListaSustitucion [] [] = []
armarListaSustitucion (x:xs) (e:es) = (x,e):(armarListaSustitucion xs es)


-- Evaluación completa
strong :: Exp -> V
strong e = case weak e of
    ConsW k es -> ConsV k (map strong es)
    LamW x e' -> LamV x e'

-- semántica/reglas evaluación completa:

--     e ↓ λx.e' 
--    ――――――――――――
--     e ↓_ λx.e'

--      e ↓ k e̅     e̅ ↓_ v̅ 
--    ――――――――――――――――――――――――
--           e ↓_ k v̅


-- FUNCIONES
-- Or
-- Chi puro:
{-
\b1. \b2. case b1 of [
    True -> [], True,
    False -> [], b2
]
-}
-- Chi embebido:
orChi :: Exp
orChi = Lam "b1" (Lam "b2" (Case (Var "b1") [
        ("True", ([], Cons "True" [])),
        ("False", ([], Var "b2"))
    ]))

-- Triple
-- Chi puro:
{-
rec triple. \n. case n of [
    Z -> [], Z[],
    S -> [n'], S[S[S[triple n'[]]]]
] 
-}
-- Chi embebido:
triple :: Exp
triple = Rec "triple" (Lam "n" (Case (Var "n") [
    ("Z", ([], Cons "Z" [])),
    ("S", (["n'"], (Cons "S" [Cons "S" [Cons "S" [App (Var "triple" ) (Var "n'")]]]) ))
    ]))

-- Duplicar
-- Chi puro:
{- 
rec duplicar. \l. case l of [
    [] -> [], [] [],
    : -> [x, xs], :[x, :[x, duplicar xs]]
]
-}
-- Chi embebido:
duplicar :: Exp
duplicar = Rec "duplicar" (Lam "l" (Case (Var "l") [
    ( "[]", ( [] , Cons "[]" [] ) ),
    ( ":", ( ["x","xs"] , Cons ":" [ Var "x" , Cons ":" [ Var "x" , App (Var "duplicar") (Var "xs") ] ] ) )
    ]))

-- RamaC
-- árbol: constructores "H" (hoja) y "N" (nodo, con dato, izq, centro y der)
-- Chi puro: 
{-
rec ramaC. \t. case t of [
    H -> [x], :[x, []],
    N -> [x, i, c, d], :[x, ramaC c]
]
-}
--Chi embebido:
ramaC :: Exp
ramaC = Rec "ramaC" (Lam "t" (Case (Var "t") [
    ( "H", ( ["x"] , Cons ":" [Var "x" , Cons "[]" []] ) ),
    ("N", (["x","i","c","d"], Cons ":" [ Var "x" , App (Var "ramaC") (Var "c") ] ) )
    ]))

-- Zeros
-- Chi puro:
{-
rec zeros. : [Z [], zeros]   -- version 1
rec zeros. (: [Z []]) zeros] -- version 2
-}
-- Chi embebido:
zeros :: Exp
zeros = Rec "zeros" (App (Cons ":" [Cons "Z" []]) (Var "zeros"))

-- Takes
--Chi puro:
{-
rec takes. \n. \xs. case n of [
    Z -> [], [] [],
    S -> [n'], case xs of [                   -- acá podrían usar n si quisieran pero preferí distinguir
        [] -> [] [],
        :  -> [x, xs'] : [x, (takes n') xs']  -- lo mismo, podrían usar xs de nuevo
    ]
]
-}
-- Chi embebido:
takes :: Exp
takes = Rec "takes" (Lam "n" (Lam "xs" (Case (Var "n") [
        ("Z", ([], Cons "[]" [])),
        ("S", (["n'"], Case (Var "xs") [
            ("[]", ([], Cons "[]" [])),
            (":", (["x", "xs'"], Cons ":" [Var "x", App (App takes (Var "n'")) (Var "xs'")]))
        ]))
    ])))

-- Not
-- Chi puro:
{-
\b. case b of [
    True -> [], False [],
    False -> [], True []
]
-}
--Escribir explicitamente la derivación en deducción natural del juicio de evalución débil para las expresiones de χ:
-- not (False []):
{-                                                                       cons ――――――――
                                                                               True []
                               cons ――――――――――――――――――――――――        efecto ――――――――――――――――――
                                       False [] ↓ False []                  True [] [[]:=[]]  ↓  True[]
                               case ――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                                       case False [] of [True -> [], False [], False -> [], True []]
      abs ―――――――――――――      efecto ――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
            not ↓ not                case b of [True -> [], False [], False -> [], True []] [b:=False []] ↓ True []
    app-B ―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                    ( \b. case b of [True -> [], False [], False -> [], True []] )( False [] ) ↓ True []
-}
-- not (not (True [])):
{-                                                                                    cons ―――――――――
                                                                                           False []
                                               cons ――――――――――――――――――――        efecto ――――――――――――――――――
                                                     True [] ↓ True []                  False [] [[]:=[]]  ↓  False[]
                                               case ――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                                                      case True [] of [True -> [], False [], False -> [], True []]
                          abs ――――――――――   ――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――― efecto    cons ――――――――
                               not ↓ not   case b of [True -> [], False [], False -> [], True []] [b:=True []] ↓ False []                  True []
                        app-B ―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――    efecto ―――――――――――――――――
                                 not (True []) ↓ False []                                                                             True [] [[]:=[]]  ↓  True[]
                         case ―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                                  case not (True []) of [True -> [], False [], False -> [], True []]
    abs ―――――――――――――  efecto ――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
          not ↓ not            case b of [True -> [], False [], False -> [], True []] [b:=not (True [])] ↓ True []
  app-B ―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――
                                               not (not (True [])) ↓ True []
-}

{- Ejercicio 4: Es necesaria la sutitución múltiple ya que no se obtiene el mismo resultado iterando sustituciones simples. 
 El orden de aplicación de sustituciones simples puede afectar el resultado cuando las variables se pisan entre sí.
 Por ejemplo: x [x := y, y := Z] --> con sustitución mútiple quedaría y
                                 --> con sustitución simple iterada quedaría y en el primer paso, pero Z al final
 Otro ejemplo: ("Pair" [x, y]) [x := y][y := z]  → ("Pair" [z, z]) / sustitución simple
               ("Pair" [x, y]) [x := y, y := z]  → ("Pair" [y, z]) / sustitucion mútliple

-}

-- Ejercicio 9:
-- semántica:
--   e ↓ True[]    e'↓ w
--  ――――――――――――――――――――――――――― if-true
--   If e then e' else e'' ↓ w


--   e ↓ False[]    e'' ↓ w
--  ――――――――――――――――――――――――――― if-false
--   If e then e' else e'' ↓ w

-- d) No, las reglas definidas no aplican para 3 expresiones cualquiera dado que es necesario que la primera expresión evalúe a True[] o False[].
-- De otro modo, la expresión If y las reglas no tendrían sentido.


-- PRUEBAS
-- Or:
assertOrExpectedOutcome1 :: Bool
assertOrExpectedOutcome1 = strong (App (App orChi (Cons "True" [])) (Cons "False" [])) == (ConsV "True" [])
assertOrExpectedOutcome2 :: Bool
assertOrExpectedOutcome2 = strong (App (App orChi (Cons "True" [])) (Cons "True" [])) == (ConsV "True" [])
assertOrExpectedOutcome3 :: Bool
assertOrExpectedOutcome3 = strong (App (App orChi (Cons "False" [])) (Cons "False" [])) == ConsV "False" []
-- Triple:
assertOrExpectedOutcome4 :: Bool
assertOrExpectedOutcome4 = strong (App triple (Cons "Z" [])) == ConsV "Z" []
assertOrExpectedOutcome5 :: Bool
assertOrExpectedOutcome5 = strong (App triple (Cons "S" [Cons "Z" []])) == ConsV "S" [ConsV "S" [ConsV "S" [ConsV "Z" []]]]
assertOrExpectedOutcome6 :: Bool
assertOrExpectedOutcome6 = strong (App triple (Cons "S" [Cons "S" [Cons "Z" []]])) == ConsV "S" [ConsV "S" [ConsV "S" [ConsV "S" [ConsV "S" [ConsV "S" [ConsV "Z" []]]]]]]
-- Duplicar:
assertOrExpectedOutcome7 :: Bool
assertOrExpectedOutcome7 = strong (App duplicar (Cons "[]" [])) == ConsV "[]" []
assertOrExpectedOutcome8 :: Bool
assertOrExpectedOutcome8 = strong (App duplicar (Cons ":" [Cons "1" [], Cons ":" [Cons "2" [], Cons "[]" []]])) == ConsV ":" [ConsV "1" [],
                                                                                                                   ConsV ":" [ConsV "1" [],
                                                                                                                   ConsV ":" [ConsV "2" [],
                                                                                                                   ConsV ":" [ConsV "2" [], ConsV "[]" []]]]]
-- RamaC:
assertOrExpectedOutcome9 :: Bool
assertOrExpectedOutcome9 = strong (App ramaC (Cons "H" [Cons "c" []])) == ConsV ":" [ConsV "c" [], ConsV "[]" []]
assertOrExpectedOutcome10 :: Bool
assertOrExpectedOutcome10 = strong (App ramaC (Cons "N" [Cons "c1" [], 
                                                         Cons "H" [Cons "a" []], 
                                                         Cons "N" [Cons "c2" [], 
                                                                   Cons "H" [Cons "b" []], 
                                                                   Cons "H" [Cons "c3" []], 
                                                                   Cons "H" [Cons "d" []]], 
                                                         Cons "H" [Cons "e" []]])) 
                            == ConsV ":" [ConsV "c1" [], ConsV ":" [ConsV "c2" [], ConsV ":" [ConsV "c3"[], ConsV "[]" []]]]
-- Takes:
assertOrExpectedOutcome11 :: Bool
assertOrExpectedOutcome11 = strong (App (App takes (Cons "Z" [])) (Cons ":" [Cons "Z" [], Cons "[]" []])) == ConsV "[]" []
assertOrExpectedOutcome12 :: Bool
assertOrExpectedOutcome12 = strong (App (App takes (Cons "S" [Cons "S" [Cons "Z" []]])) (Cons ":" [Cons "a" [], 
                                                                                         Cons ":" [Cons "b" [],
                                                                                         Cons ":" [Cons "c" [], 
                                                                                         Cons "[]" [] ]]])) 
                            == ConsV ":" [ConsV "a" [], ConsV ":" [ConsV "b" [], ConsV "[]" []]]
--------------------------------------------------------------------------------------------------------------------------------------------------------------
main :: IO ()
main = do
    print assertOrExpectedOutcome1
    print assertOrExpectedOutcome2
    print assertOrExpectedOutcome3
    print assertOrExpectedOutcome4
    print assertOrExpectedOutcome5
    print assertOrExpectedOutcome6
    print assertOrExpectedOutcome7
    print assertOrExpectedOutcome8
    print assertOrExpectedOutcome9
    print assertOrExpectedOutcome10
    print assertOrExpectedOutcome11
    print assertOrExpectedOutcome12