import LookupTable

data Expr = 
            Variable Var
        |   ConjVacio  
        |   ConjUnitario Z
        |   Pertenencia Z Expr
        |   Union Expr Expr
        |   Interseccion Expr Expr
        |   Diferencia Expr Expr
        |   Inclusion Expr Expr
        |   Asignacion Var Expr
        -- parte 6
        |   Partes Expr
        |   Igualdad Expr Expr

type Var = String -- x
type Z = Integer

data Val = Conjunto [Z] 
        |   Booleano Bool 
        -- parte 6
        |   ConjuntoPartes [[Z]]
        deriving (Show)

type Memory = LookupTable.Table Var Val

-- EVAL
eval :: (Memory, Expr) -> (Memory, Val)
eval (m, Variable x) = case LookupTable.lkup x m of 
    Just v -> (m, v)
eval (m, ConjVacio) = (m, Conjunto [])
eval (m, ConjUnitario z) = (m, Conjunto [z])
eval (m, Pertenencia z e) = case eval (m,e) of
    (m', Conjunto c) -> (m', Booleano (belongs z c))
eval (m, Union e1 e2) = case eval (m, e1) of
    (m', Conjunto c1) -> case eval (m', e2) of
        (m'', Conjunto c2) -> (m'', Conjunto (union c1 c2))
eval (m, Interseccion e1 e2) = case eval (m, e1) of
    (m', Conjunto c1) -> case eval (m', e2) of
        (m'', Conjunto c2) -> (m'', Conjunto (intersection c1 c2))
eval(m, Diferencia e1 e2) = case eval (m, e1) of
    (m', Conjunto c1) -> case eval (m', e2) of
        (m'', Conjunto c2) -> (m'', Conjunto (difference c1 c2))
eval(m, Inclusion e1 e2) = case eval (m, e1) of
    (m', Conjunto c1) -> case eval (m', e2) of
        (m'', Conjunto c2) -> (m'', Booleano (included c1 c2))
eval(m, Asignacion x e) = case eval(m, e) of
    (m', v) -> (LookupTable.upd (x,v) m', v)
-- parte 6
eval (m, Partes e) = case eval (m,e) of
    (m', Conjunto c) -> (m', ConjuntoPartes (partes c))
eval(m, Igualdad e1 e2) = case eval (m, e1) of
    (m', Conjunto c1) -> case eval (m', e2) of
        (m'', Conjunto c2) -> (m'', Booleano (iguales c1 c2))


-- F. aux.
-- belongs, que dado un entero z y un conjunto c, retorna True si z se encuentra en c. ES ELEM
belongs :: Integer -> [Integer] -> Bool
belongs z [] = False
belongs z (x:xs)
    | x==z = True
    | otherwise = belongs z xs
-- belongs z xs = elem z xs

-- union, que dados 2 conjuntos c1 y c2, retorna un nuevo conjunto con los elementos de ambos conjuntos.
union :: [Integer] -> [Integer] -> [Integer]
union c1 c2 = eliminarRepetidos (c1 ++ c2) -- nub(c1++c2) importando Data.List

eliminarRepetidos :: [Integer] -> [Integer]
eliminarRepetidos [] = []
eliminarRepetidos (x:xs)
    | belongs x xs = eliminarRepetidos xs
    | otherwise = x:(eliminarRepetidos xs)

-- intersection, que dados 2 conjuntos c1 y c2, retorna un nuevo conjunto con los elementos que c1 y c2 tienen en común.
intersection :: [Integer] -> [Integer] -> [Integer]
intersection [] c2 = []
intersection c1 [] = []
intersection (x:xs) c2
    | belongs x c2 == False = intersection xs c2
    | otherwise = x:(intersection xs c2)

-- difference, que dados 2 conjuntos c1 y c2, retorna un nuevo conjunto con los elementos de c1, que no se encuentren en c2.
difference :: [Integer] -> [Integer] -> [Integer]
difference [] c2 = []
difference (x:xs) c2
    | belongs x c2 == False = x:(difference xs c2)
    | otherwise = difference xs c2

-- included, que dados 2 conjuntos c1 y c2, retorna True si todos los elementos de c1 se encuentran en c2.
included :: [Integer] -> [Integer] -> Bool
included [] c2 = True
included (x:xs) c2 
    | belongs x c2 == False = False
    | otherwise = included xs c2

--parte 6
-- partes: dado un conjunto c, devuelve su conjunto potencia.
partes :: [Integer] -> [[Integer]]
partes [] = [[]]
partes (x:xs) = (partes xs) ++ map (x:) (partes xs)

-- iguales: dados dos conjuntos, retorna True si son iguales (si y solo si tienen los mismos elementos).
iguales :: [Integer] -> [Integer] -> Bool
iguales [] [] = True
iguales c1 c2 = (included c1 c2) && (included c2 c1)

-- EXPRESIONES
conj1 :: Expr
conj1 = Union (Union (ConjUnitario 1) (ConjUnitario 2)) (ConjUnitario 3) -- {1,2,3}

conj2 :: Expr
conj2 = Union (Union (ConjUnitario 2) (ConjUnitario 3)) (ConjUnitario 4) --{2,3,4}

conj3 :: Expr
conj3 = Union conj1 conj2 -- {1,2,3} ∪ {2,3,4} -> {1,2,3,4}

conj4 :: Expr
conj4 = Interseccion conj1 conj2 -- {1,2,3} ∩ {2,3,4} -> {2,3}

pert1 :: Expr
pert1 = Pertenencia 2 conj1 -- 2 ∈ {1,2,3} -> True

pert2 :: Expr
pert2 = Pertenencia 3 conj4 -- 3 ∈ ({1,2,3} ∩ {2,3,4}) -> True

incl1 :: Expr
incl1 = Inclusion conj1 conj2 -- {1,2,3} ⊆ {2,3,4} -> False

incl2 :: Expr
incl2 = Inclusion conj4 conj2 -- ({1,2,3} ∩ {2,3,4}) ⊆ {2,3,4} -> True

incl3 :: Expr
incl3 = Inclusion conj1 conj3 -- {1,2,3} ⊆ ({1,2,3} ∪ {2,3,4}) -> True

ass1 :: Expr
ass1 = Asignacion "w" conj1 -- w := {1,2,3}

ass2 :: Expr
ass2 = Asignacion "x" conj4 -- x := {1,2,3} ∩ {2,3,4}

ass3 :: Expr
ass3 = Asignacion "y" pert2 -- y := 3 ∈ ({1,2,3} ∩ {2,3,4})

ass4 :: Expr
ass4 = Asignacion "z" incl2 -- z := ({1,2,3} ∩ {2,3,4}) ⊆ {2,3,4}