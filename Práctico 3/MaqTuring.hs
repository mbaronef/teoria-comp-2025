{-# OPTIONS_GHC -fno-warn-tabs #-}
import LookupTable

type Alphabet = String

data State = Init 
            | Halt
            | Q String
    deriving (Eq, Show)

data Action = LeftA
             | RightA
             | Write String
    deriving (Eq, Show)

type Tape = ([Alphabet], Alphabet, [Alphabet])

type Branch = LookupTable.Table Alphabet (Action, State)

type TuringMachine = LookupTable.Table State Branch

executeAction :: Tape -> Action -> Tape
executeAction (l, c, r) LeftA = case l of
    [] -> ([], "#", c:r)
    otherwise -> (init l, last l, c:r)
executeAction (l, c, r) RightA = case r of
    [] -> (l++[c], "#", r)
    r':rs -> (l ++ [c], r',  rs)
executeAction (l, c, r) (Write s) = (l, s, r)

executeCode :: Tape -> TuringMachine -> Tape
executeCode (l,c,r) tm = case LookupTable.lkup Init tm of
    Just b -> case LookupTable.lkup c b of
        Just (a,s) -> fst (executeSteps ((executeAction (l,c,r) a), s) tm )
        Nothing -> case LookupTable.lkup "_" b of
            Just(a',s') -> fst (executeSteps ((executeAction (l,c,r) a'), s') tm )
    Nothing -> (l,c,r)

executeStep :: (Tape, State) -> TuringMachine -> (Tape, State)
executeStep ((l,c,r), state) tm = case LookupTable.lkup state tm of
    Just b -> case LookupTable.lkup c b of
        Just (a, s) -> (executeAction (l,c,r) a, s)
        Nothing -> case LookupTable.lkup "_" b of
            Just (a, s) -> (executeAction (l, c, r) a, s)

executeSteps :: (Tape, State) -> TuringMachine -> (Tape, State)
executeSteps (tape, state) tm = case state of
    Halt -> (tape, state)
    otherwise -> executeSteps (executeStep (tape, state) tm) tm


-- 3. MT Embebidas en Haskell --
lsigma :: Alphabet -> TuringMachine
lsigma s = [
    (Init, [("_",(LeftA, Q "loop"))]),
    (Q "loop", [
                (s, (Write s, Halt)),
                ("_", (LeftA, Q "loop"))
                ])
    ]

par :: TuringMachine 
-- revisar, inventé que el cabezal arranque en # antes de la tira y termine en el T/F después de la tira (con separador #).
par = [
    (Init, [("_",(RightA, Q "par"))]),
    (Q "par", [
                ("sigma", (RightA, Q "impar")),
                ("_", (RightA, Q "verdadero"))
                ]),
    (Q "impar", [
                ("sigma", (RightA, Q "par")),
                ("_", (RightA, Q "falso"))
                ]),
    (Q "falso", [("_", (Write "F", Halt))]),
    (Q "verdadero", [("_", (Write "T", Halt))])
    ]

elemsigma :: Alphabet -> TuringMachine 
-- revisar, pasa lo mismo que en par. Inventé yo donde arranca y termina el cabezal.
elemsigma s = [
    (Init, [("_",(RightA, Q "buscar"))]),
    (Q "buscar", [
                (s, (RightA, Q "encontrado")),
                ("#", (RightA, Q "falso")), -- ("_", (RightA, Q "buscar")) al final
                ("_", (RightA, Q "buscar")) -- ("sigma1", (RightA, Q "buscar")), ("sigma2", (RightA, Q "buscar")),
                ]),
    (Q "encontrado", [
                (s, (RightA, Q "encontrado")),
                ("#", (RightA, Q "verdadero")), -- ("_", (RightA, Q "verdadero")) al final
                ("_", (RightA, Q "encontrado")) -- ("sigma1", (RightA, Q "encontrado")), ("sigma2", (RightA, Q "encontrado")),
                ]),
    (Q "falso", [("_", (Write "F", Halt))]),
    (Q "verdadero", [("_", (Write "T", Halt))])
    ]

reverseMT :: TuringMachine -- seguí las convenciones(? que vimos en clase
reverseMT = [
    (Init, [("_",(LeftA, Q "marcar"))]),
    (Q "marcar", [
                ("sigma1", (Write "M", Q "avanzar1S1")),
                ("sigma2", (Write "M", Q "avanzar1S2")),
                ("#", (RightA, Q "primer#"))
                ]),
    (Q "avanzar1S1", [("M", (RightA, Q "primer#S1"))]),
    (Q "primer#S1", [
                ("#", (RightA, Q "escribirS1")),
                ("_", (RightA, Q "primer#S1"))
                ]),
    (Q "escribirS1", [
                ("#", (Write "sigma1", Q "volverAMarcaS1")),
                ("_", (RightA, Q "escribirS1"))
                ]),
    (Q "volverAMarcaS1", [
                ("M", (Write "sigma1", Q "seguirMarcando")),
                ("_", (LeftA, Q "volverAMarcaS1"))
                ]),
    (Q "avanzar1S2", [("M", (RightA, Q "primer#S2"))]),
    (Q "primer#S2", [
                ("#", (RightA, Q "escribirS2")),
                ("_", (RightA, Q "primer#S2"))
                ]),
    (Q "escribirS2", [
                ("#", (Write "sigma2", Q "volverAMarcaS2")),
                ("_", (RightA, Q "escribirS2"))
                ]),
    (Q "volverAMarcaS2", [
                ("M", (Write "sigma2", Q "seguirMarcando")),
                ("_", (LeftA, Q "volverAMarcaS2"))
                ]),
    (Q "seguirMarcando", [("_", (LeftA, Q "marcar"))]),
    (Q "primer#", [
                ("#", (RightA, Q "irAlFin")),
                ("_", (RightA, Q "primer#"))
                ]),
    (Q "irAlFin", [
                ("#", (Write "#", Halt)),
                ("_", (RightA, Q "irAlFin"))
                ])
    ]

-- TESTS LSIGMA
tapePrueba1 :: Tape
tapePrueba1 = (["#", "sigma", "A"], "#", [])
tapeNueva1 :: Tape
tapeNueva1 = executeCode tapePrueba1 (lsigma "sigma")

testLSigma1 :: Bool
testLSigma1 = tapeNueva1 == (["#"], "sigma", ["A", "#"])

-- TESTS PAR
tapePrueba2 :: Tape
tapePrueba2 = ([], "#", ["sigma","sigma", "sigma"])
tapeNueva2 :: Tape
tapeNueva2 = executeCode tapePrueba2 par 

testPar1:: Bool
testPar1 = tapeNueva2 == (["#", "sigma", "sigma", "sigma", "#"], "F", [])

-- TESTS ELEMSIGMA
tapePrueba3 :: Tape
tapePrueba3 = ([], "#", ["sigma1","sigma2", "sigma1", "#"])
tapeNueva3 :: Tape
tapeNueva3 = executeCode tapePrueba3 (elemsigma "sigma")

testElemSigma1:: Bool
testElemSigma1 = tapeNueva3 == (["#", "sigma1", "sigma2", "sigma1", "#"], "F", [])

tapePrueba4 :: Tape
tapePrueba4 = ([], "#", ["sigma1","sigma", "sigma2", "#"])
tapeNueva4 :: Tape
tapeNueva4 = executeCode tapePrueba4 (elemsigma "sigma")

testElemSigma2:: Bool
testElemSigma2 = tapeNueva4 == (["#", "sigma1", "sigma", "sigma2", "#"], "T", [])

-- TEST REVERSE
tapePrueba5 :: Tape
tapePrueba5 = (["sigma1","sigma2", "sigma2"], "#", [])
tapeNueva5 :: Tape
tapeNueva5 = executeCode tapePrueba5 reverseMT 

testReverse1:: Bool
testReverse1 = tapeNueva5 == (["#","sigma1","sigma2","sigma2","#","sigma2", "sigma2", "sigma1"], "#", [])

tapePrueba6 :: Tape
tapePrueba6 = (["sigma1", "sigma1"], "#", [])
tapeNueva6 :: Tape
tapeNueva6 = executeCode tapePrueba6 reverseMT 

testReverse2 :: Bool
testReverse2 = tapeNueva6 == (["#","sigma1", "sigma1", "#", "sigma1", "sigma1"], "#", [])

tapePrueba7 :: Tape
tapePrueba7 = (["sigma2"], "#", [])
tapeNueva7 :: Tape
tapeNueva7 = executeCode tapePrueba7 reverseMT 

testReverse3 :: Bool
testReverse3 = tapeNueva7 == (["#","sigma2", "#", "sigma2"], "#",[])

tapePrueba8 :: Tape
tapePrueba8 = ([], "#", [])
tapeNueva8 :: Tape
tapeNueva8 = executeCode tapePrueba8 reverseMT 

testReverse4 :: Bool
testReverse4 = tapeNueva8 == (["#", "#"], "#", [])