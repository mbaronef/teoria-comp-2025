-- IMPORTS
import Data.List (nub, lookup) 
-------------------------------------------------------------------------------------------------------------------
-- 3-SAT
-- Dominio y solución
type Termino = (String, Bool)
type Clausula = (Termino, Termino, Termino)

type DomA = [Clausula]
type SolA = [Termino] -- asignación/valuación

-- Verificador en tiempo polinomial
verifyA :: (DomA, SolA) -> Bool
verifyA ([], asignacion) = True
verifyA ((c:cs), asignacion) = (clausulaTrue c asignacion) && (verifyA (cs,asignacion))

clausulaTrue :: Clausula -> SolA -> Bool -- Verifica si al menos un literal está satisfecho en la asignación
clausulaTrue (t1, t2, t3) asignacion = evalLit t1 asignacion || evalLit t2 asignacion || evalLit t3 asignacion

evalLit :: Termino -> SolA -> Bool
evalLit (var, val) asignacion = case lookup var asignacion of
    Just b -> b == val
    Nothing -> False 

-- Resolución en tiempo exponencial
solveA :: DomA -> SolA
solveA formula = buscarSolucionA formula (generarValuaciones formula)

generarValuaciones :: DomA -> [SolA] -- generar las 2^n posibles asignaciones
generarValuaciones formula =
  let vars = variables formula
  in asignaciones vars

variables :: DomA -> [String] -- Extrae variables únicas de la fórmula
variables formula = nub (concat (map variablesClausula formula))

variablesClausula :: Clausula -> [String]
variablesClausula (t1, t2, t3) = map fst [t1, t2, t3]

asignaciones :: [String] -> [SolA] -- Genera todas las combinaciones posibles de True/False para una lista de variables
asignaciones [] = [[]]
asignaciones (v:vs) =
  let resto = asignaciones vs
  in [(v, True):r | r <- resto] ++ [(v, False):r | r <- resto]

buscarSolucionA :: DomA -> [SolA] -> SolA
buscarSolucionA _ [] = []
buscarSolucionA dom (a:as)
  | verifyA (dom, a) = a
  | otherwise = buscarSolucionA dom as
------------------------------------------------------------------------------------------------------------------------------
-- OPTIMIZACIÓN DE INVERSIONES INTERNAS CON DEPENDENCIAS ENTRE GRUPOS DE PROYECTOS
-- Dominio y solución
type Nombre = String
type Costo = Int
type Cmax = Int -- presupuesto máximo

type Beneficio = Int
type Bmin = Int

type P = (Nombre, Costo, Beneficio) -- Proyecto

type G = [Nombre] -- Grupos, cada grupo es una lista de nombres de proyectos a los que pertenece.

type DomB = ([P], [G], Cmax, Bmin)
type SolB = [Nombre] -- lista de nombres de proyectos seleccionados

-- Verificador en tiempo polinomial
verifyB :: (DomB, SolB) -> Bool
verifyB ((proyectos, grupos, cmax, bmin), sol) = (gruposCompletos grupos sol) 
    && ((costoTotal proyectos sol) <= cmax) 
    &&((beneficioTotal proyectos sol) >= bmin)

costoTotal :: [P] -> SolB -> Costo
costoTotal ps sol = sum [c | (n, c, _) <- ps, n `elem` sol]

beneficioTotal :: [P] -> SolB -> Beneficio
beneficioTotal ps sol = sum [b | (n, _, b) <- ps, n `elem` sol]

gruposCompletos :: [G] -> SolB -> Bool
gruposCompletos grupos sol = all grupoValido grupos
  where
    grupoValido grupo = 
      let ningunoEnSol = not (any (`elem` sol) grupo)
          todosEnSol  = all (`elem` sol) grupo
      in ningunoEnSol || todosEnSol

-- Resolución en tiempo exponencial
solveB :: DomB -> SolB
solveB (proyectos, g, c, b) =
  let nombresProyectos = map (\(n, _, _) -> n) proyectos
      dom = (proyectos, g, c, b)
  in buscarSolucionB dom (subconjuntos nombresProyectos)

subconjuntos :: [Nombre] -> [[Nombre]] -- Genera todos los subconjuntos posibles de nombres de proyectos
subconjuntos [] = [[]]
subconjuntos (x:xs) =
  let resto = subconjuntos xs
  in resto ++ map (x:) resto

buscarSolucionB :: DomB -> [SolB] -> SolB
buscarSolucionB _ [] = []
buscarSolucionB dom (s:ss)
  | verifyB (dom, s) = s
  | otherwise = buscarSolucionB dom ss
-------------------------------------------------------------------------------------------------------------------------------
-- TESTS 
-- 3-SAT
tests3SAT :: Bool
tests3SAT = test3SAT1 && test3SAT2 && test3SAT3 && test3SAT4 && test3SAT5 && test3SAT6 && test3SAT7 && test3SAT8 && test3SAT9 && test3SAT10

formula1 :: DomA -- (x ∨ ¬y ∨ z) ∧ (¬x ∨ y ∨ ¬z)
formula1 = [ (("x", True), ("y", False), ("z", True))
           , (("x", False), ("y", True), ("z", False)) ]

formula2 :: DomA -- (x ∨ y ∨ z)
formula2 = [(("x", True), ("y", True), ("z", True))]

formulaVacia :: DomA
formulaVacia = []

formulaInsat :: DomA -- (x ∨ x ∨ x) ∧ (¬x ∨ ¬x ∨ ¬x) No hay asignación que cumpla ambas
formulaInsat = [(("x", True), ("x", True), ("x", True)), (("x", False), ("x", False), ("x", False))]

asignacion1 :: SolA 
asignacion1 = [("x", True), ("y", True), ("z", True)]

asignacion2 :: SolA 
asignacion2 = [("x", True), ("y", False), ("z", True)]

asignacion3 :: SolA
asignacion3 = [("x", True), ("y", False), ("z", True), ("w", True)]

asignacion4 :: SolA 
asignacion4 = [("x", False), ("y", False), ("z", False)]

asignacionVacia :: SolA
asignacionVacia = []

test3SAT1 :: Bool
test3SAT1 = verifyA (formula1, asignacion1) == True

test3SAT2 :: Bool
test3SAT2 = verifyA (formula1, asignacion2) == False

test3SAT3 :: Bool
test3SAT3 = verifyA (formula1, asignacion3) == False

test3SAT4 :: Bool
test3SAT4 = verifyA (formula1, solveA formula1) == True

test3SAT5 :: Bool
test3SAT5 = verifyA (formula2, asignacion1) == True

test3SAT6 :: Bool
test3SAT6 = verifyA (formula2, asignacion4) == False

test3SAT7 :: Bool
test3SAT7 = verifyA (formula2, solveA formula2) == True

test3SAT8 :: Bool
test3SAT8 = verifyA (formulaVacia, asignacionVacia) == True

test3SAT9 :: Bool
test3SAT9 = verifyA (formulaInsat, solveA formulaInsat) == False

test3SAT10 :: Bool
test3SAT10 = solveA formulaInsat == []

-- OPTIMIZACIÓN DE INVERSIONES INTERNAS CON DEPENDENCIAS ENTRE GRUPOS DE PROYECTOS
testsB :: Bool
testsB = testB1 && testB2 && testB3 && testB4 && testB5 && testB6 && testB7 && testB8

domB1 :: DomB
domB1 = ([("p1", 5, 10), ("p2", 5, 15)], -- proyectos
  [["p1", "p2"]], -- un grupo con dos proyectos
  15, -- cmax
  20  -- bmin
  )

solB1 :: SolB
solB1 = ["p1"] -- al tener dependencia con p2, faltan proyectos

testB1 :: Bool
testB1 = verifyB (domB1, solB1) == False

domB2 :: DomB
domB2 = ([("p1", 5, 10), ("p2", 6, 10), ("p3", 3, 5)],
         [["p1", "p2"], ["p3"]],
         12,  -- presupuesto máximo justo para p1 + p2
         20)  -- beneficio mínimo igual a la suma de p1 + p2

solB2 :: SolB
solB2 = ["p1", "p2"]

solB2Fallo :: SolB
solB2Fallo = ["p1"] -- grupo incompleto

testB2 :: Bool
testB2 = verifyB (domB2, solB2) == True -- grupo completo y cumple presupuesto y beneficio

testB3 :: Bool
testB3 = verifyB (domB2, solB2Fallo) == False

domB3 :: DomB
domB3 = ([("p1", 4, 10), ("p2", 4, 15), ("p3", 5, 12), ("p4", 2, 5)],
         [["p1", "p2"], ["p3", "p4"]],
         10,
         25)

testB4 :: Bool
testB4 = verifyB (domB3, (solveB domB3)) == True

domB4 :: DomB
domB4 = ([("p1", 10, 5), ("p2", 10, 5)],
         [["p1", "p2"]],
         15,  -- presupuesto menor que costo total
         20)  -- beneficio alto

testB5 :: Bool
testB5 = verifyB (domB4, (solveB domB4)) == False -- no hay solución porque presupuesto insuficiente

domB5 :: DomB
domB5 = ([("p1", 5, 10), ("p2", 6, 15), ("p3", 3, 5), ("p4", 2, 20)],
         [["p1", "p2"]], 
         10,
         10)

testB6 :: Bool
testB6 = verifyB (domB5, ["p3"]) == False -- p3 está solo, cumple presupuesto y pero no beneficio

testB7 :: Bool
testB7 = verifyB (domB5, ["p4"]) == True -- p4 está solo, cumple presupuesto y  beneficio

testB8 :: Bool
testB8 = verifyB (domB5, (solveB domB5)) == True