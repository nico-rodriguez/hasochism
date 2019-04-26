-- promover Tipos a nivel de Kinds
{-# LANGUAGE DataKinds             #-}
-- activar Data Types Generalizados
{-# LANGUAGE GADTs                 #-}
-- permitir la escritura del Kind en los tipos
{-# LANGUAGE KindSignatures        #-}
-- habilita las Type Families
{-# LANGUAGE TypeFamilies          #-}
-- poder usar nombres de operadores (infijos) al usar y definir Tipos
{-# LANGUAGE TypeOperators         #-}
-- permitir tipos de rango arbitrario (colocar la cuantificación al lado de
-- ellos, ver la función natter)
{-# LANGUAGE RankNTypes            #-}
-- permitir classes con más de un parámetro
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE FlexibleInstances     #-}

{-# LANGUAGE FlexibleContexts      #-}

{-# LANGUAGE PolyKinds             #-}


module Main where

import           Data.Proxy

-- Capítulo 2: A Variety of Cuantifiers ########################################

-- Data Type de los Naturales
data Nat = Z | S Nat deriving (Show, Eq, Ord)

-- Data Type de los Vectores
data Vec::Nat -> * -> * where
  V0    ::                 Vec 'Z x
  (:>)  :: x -> Vec n x -> Vec ('S n) x

-- Chequear la suma a nivel de tipos. La función :+ recibe dos tipos y retorna
-- el tipo que representa la suma.
type family (m::Nat) :+ (n::Nat) :: Nat
type instance 'Z    :+ n = n
type instance 'S m  :+ n = 'S(m :+ n)

-- Chequear que el largo del vector resultado sea igual al largo de la suma
-- de los parámetros. El chequeo se hace a nivel de tipos.
vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
vappend V0        ys = ys
vappend (x :> xs) ys = x :> vappend xs ys

vappendExample :: Vec ('S ('S ('S 'Z))) Nat
vappendExample = vappend (Z :> V0) (Z :> (Z :> V0))

-- Esta primera versión está mal, porque se necesita m en tiempo de ejecución
-- y se necesita hacer referencia a él explícitamente.
-- vchop :: Vec (m :+ n) x -> (Vec m x, Vec n x)

-- Para resolverlo, se define el Tipo de los Natty como un Singleton GADT.
-- Cada Tipo n tiene un representante único de Tipo Natty n.
data Natty :: Nat -> * where
  Zy :: Natty 'Z
  Sy :: Natty n -> Natty ('S n)

-- Ahora se puede hacer referencia explícitamente a m en tiempo de ejecución:
vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
vchop Zy      xs        = (V0, xs)
vchop (Sy n)  (x :> xs) = (x :> ys, zs)
  where
    (ys, zs) = vchop n xs

vchopExample :: (Vec ('S 'Z) Nat, Vec ('S ('S 'Z)) Nat)
vchopExample = vchop (Sy Zy) vappendExample

-- En esta primera versión de vtake, el tipo de n es ambiguo. A diferencia de
-- antes, el n ahora no aparece en el resultado.
-- vtake :: Natty m -> Vec (m :+ n) x -> Vec m x
-- vtake Zy      _         = V0
-- vtake (Sy m)  (x :> xs) = x :> vtake m

-- El uso de la librería Data.Proxy permite definir proxies de Tipos con Kind
-- distinto de * (Polykinds).
-- Sin ella, solo se puede definir proxies de Tipos con Kind *.
-- e.g.: proxy = undefined :: Int
-- Usando Data.Proxy: proxy = Proxy :: Proxy Nat
-- Los proxies son para saber tipos, no import el valor del proxy (por eso
-- este puede ser undefined).

-- Para hacer explícita la información estática (el n), se usa un Proxy Type.
vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
vtake Zy      _ _         = V0
vtake (Sy m)  n (x :> xs) = x :> vtake m n xs

proxyNat :: Proxy ('S ('S 'Z))
proxyNat = Proxy :: Proxy ('S ('S 'Z))
vtakeExample :: Vec ('S 'Z) Nat
vtakeExample = vtake (Sy Zy) proxyNat (Z :> (Z :> (Z :> V0)))

proxy :: f i -> Proxy i
proxy _ = Proxy

type family Arity (n :: Nat) (x :: *)
type instance Arity 'Z     x = x
type instance Arity ('S n) x = x -> Arity n x

-- El tipo de Arity example es Int -> Int -> Int (chequearlo con ghci)
arityExample :: Arity ('S ('S 'Z)) Int
arityExample x y =  if x >= y
                      then x
                    else y

-- Pasar los n elementos del vector a una función de aridad n.
varity :: Arity n x -> Vec n x -> x
varity x V0        = x
varity f (x :> xs) = varity (f x) xs

variyExample :: Int
variyExample = varity arityExample (0 :> (1 :> V0))

-- Capítulo 3: Explicit and Implicit Pi-Types ##################################

-- Para cada Nat promovido, natty devuelve el Singleton Natty correspondiente.
-- Un NATTY se conoce en tiempo de ejecución (porque hay que verificar si
-- existe la instancia para la clase), aunque no se conozca explícitamente.
class NATTY (n :: Nat) where
  natty :: Natty n
instance NATTY 'Z where
  natty = Zy
instance NATTY n => NATTY ('S n) where
  natty = Sy natty

-- Una versión más implícita de vtake.
vtrunc :: NATTY m => Proxy n -> Vec (m :+ n) x -> Vec m x
vtrunc = vtake natty

-- 3.1: Instances for Indexed Types --------------------------------------------

-- No se necesita imponer una restricción a n, porque no se necesita su valor.
-- Solo se necesita el tipo de n para poder escribir que el vector resultado
-- tiene el mismo largo que el vector que se recibe por parámetro.
vmap :: (s -> t) -> Vec n s -> Vec n t
vmap _ V0        = V0
vmap f (s :> ss) = f s :> vmap f ss

-- Observar que no se necesita imponer una restricción de clase a n.
instance Functor (Vec n) where
  fmap = vmap

-- Se necesita saber el n en tiempo de ejecución para poder desarmarlo y
-- construir el vector.
vcopies :: Natty n -> x -> Vec n x
vcopies Zy      _ = V0
vcopies (Sy n)  x = x :> vcopies n x

-- Observar que no se necesita el valor de n en tiempo de ejecución. Solo se
-- necesita su tipo para poder decir que todos los vectores tienen el mismo
-- largo.
vapp :: Vec n (s -> t) -> Vec n s -> Vec n t
vapp V0         V0        = V0
vapp (f :> fs)  (s :> ss) = f s :> vapp fs ss

-- Como vcopies necesita conocer el largo del vector para poder armarlo,
-- es necesario agregar la restricción de clase NATTY n.
instance NATTY n => Applicative (Vec n) where
  pure  = vcopies natty
  (<*>) = vapp

instance Traversable (Vec n) where
  traverse _ V0        = pure V0
  traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

instance Foldable (Vec n) where
  foldMap = undefined

-- 3.2: Matrices and a Monad ---------------------------------------------------

data Matrix :: * -> (Nat, Nat) -> * where
  Mat :: { unMat :: Vec h (Vec w a) } -> Matrix a '(w,h)

transpose :: NATTY w => Matrix a '(w, h) -> Matrix a '(h, w)
transpose = Mat . sequenceA . unMat

-- 3.3: Exchanging Explicit and Implicit ---------------------------------------

-- A veces interesa obtener el NATTY implícito, dado que se tiene el
-- Natty n explícito. Acá se usa la extensión RankNTypes
natter :: Natty n -> (NATTY n => t) -> t
natter Zy     t = t
natter (Sy n) t = natter n t

-- Capítulo 4: An Ordered Silence ##############################################

-- La idea es demostrar que una lista está ordenada mediante la inferencia de
-- instancias de clase de Haskell. Es decir, al buscar las instancias de clase,
-- Haskell está demostrando por nosotros que la lista está ordenada.
class LeN (m :: Nat) (n :: Nat) where
instance            LeN 'Z     n     where
instance LeN m n => LeN ('S m) ('S n) where

-- Probar que dos números son oordenables de una u otra forma
-- (One Way Or The Other).
data OWOTO :: Nat -> Nat -> * where
  LE :: LeN x y => OWOTO x y
  GE :: LeN y x => OWOTO x y

owoto :: Natty m -> Natty n -> OWOTO m n
owoto Zy      _       = LE
owoto (Sy _)  Zy      = GE
owoto (Sy m)  (Sy n)  = case owoto m n of
  LE -> LE
  GE -> GE

-- Luego, se define qué significa estar ordenado entre dos cotas.
data Bound x = Bot | Val x | Top  deriving (Show, Eq, Ord)

-- Se extiende la noción de <= de la clase LeN, para que la inferencia de
-- clases chequee las cotas.
class LeB (a :: Bound Nat) (b :: Bound Nat) where
instance            LeB 'Bot     b          where
instance LeN x y => LeB ('Val x) ('Val y)   where
instance            LeB ('Val x) 'Top       where
instance            LeB 'Top 'Top           where

-- Insertar un elemento en una lista ordenada solo si el elemento es menor
-- a la cabeza. Luego, la lista resultado tiene este elemento como cabeza.
data OList :: Bound Nat -> Bound Nat -> * where
  ONil :: LeB l u         => OList l u
  (:<) :: LeB l ('Val x)  => Natty x -> OList ('Val x) u -> OList l u

-- Si ambas listas comparten las cotas, también el merge.
merge :: OList l u -> OList l u -> OList l u
merge ONil     lu        = lu
merge lu        ONil      = lu
merge (x :< xu) (y :< yu) = case owoto x y of
  LE -> x :< merge xu         (y :< yu)
  GE -> y :< merge (x :< xu)  yu

-- Ahora sabemos combinar naturales Singleton. Se construyen Singletons para
-- los números que queremos ordenar (notar el Poly Kind k en la definición).
data Ex (p :: k -> *) where
  Ex :: p i -> Ex p

-- Un wrapped Nat es un Singleton para naturales type-level.
type WNat = Ex Natty

wrapNat :: Nat -> WNat
wrapNat Z     = Ex Zy
wrapNat (S n) = case wrapNat n of Ex m -> Ex (Sy m)

deal :: [x] -> ([x], [x])
deal []     = ([], [])
deal (x:xs) = (x:zs, ys) where
  (ys, zs) = deal xs

sort :: [Nat] -> OList 'Bot 'Top
sort []   = ONil
sort [n]  = case wrapNat n of Ex m -> m :< ONil
sort xs   = merge (sort ys) (sort zs) where
  (ys, zs) = deal xs

sortExample :: OList 'Bot 'Top
sortExample = sort [S (S (S Z)), S (S Z), S Z, Z]

-- Capítulo 5: What are the Data that Go with Proofs ###########################

-- Comparar dos Singleton Nat inspeccionando su diferencia aritmética
-- (modificado más adelante).
-- data Cmp :: Nat -> Nat -> * where
--   LTNat :: Natty z -> Cmp m (m :+ 'S z)
--   EQNat ::            Cmp m m
--   GTNat :: Natty z -> Cmp (m :+ 'S z) m

cmp :: Natty m -> Natty n -> Cmp m n
cmp Zy      Zy      = EQNat
cmp Zy      (Sy n)  = LTNat n
cmp (Sy m)  Zy      = GTNat m
cmp (Sy m)  (Sy n)  = case cmp m n of
  LTNat z -> LTNat z
  EQNat   -> EQNat
  GTNat z -> GTNat z

procustres :: a -> Natty m -> Natty n -> Vec m a -> Vec n a
procustres p m n xs = case cmp m n of
  LTNat z -> vappend xs (vcopies (Sy z) p)
  EQNat   -> xs
  GTNat z -> vtake n (proxy (Sy z)) xs

-- Capítulo 6: Boxes ###########################################################

-- 6.1: Two Flavours of Conjunction --------------------------------------------

-- Definir la indexación de una tupla de dos Natty indexados.
type Size = Natty :**: Natty
data (p :: i -> *) :**: (q :: k -> *) :: (i, k) -> * where
  (:&&:) :: p i -> q k -> (p :**: q) '(i, k)

-- En este caso, los dos Natty se indexan con los mismos valores de tipo k.
data (p :: k -> *) :*: (q :: k -> *) :: k -> * where
  (:&:) :: p k -> q k -> (p :*: q) k

--6.2: The Box Data Type -------------------------------------------------------

data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p wh -> Box p wh
  Clear :: Box p wh
  Hor   :: Natty w1 -> Box p '(w1, h) ->
           Natty w2 -> Box p '(w2, h) -> Box p '(w1 :+ w2, h)
  Ver   :: Natty h1 -> Box p '(w, h1) ->
           Natty h2 -> Box p '(w, h2) -> Box p '(w, h1 :+ h2)

-- Mónadas sobre tipos indexados
type s :-> t = forall i . s i -> t i

-- Clase de las Mónadas sobre tipos indexados
class MonadIx (m :: (k -> *) -> (k -> *)) where
  returnIx :: a :-> m a
  extendIx :: (a :-> m b) -> (m a :-> m b)

instance MonadIx Box where
  returnIx                      = Stuff
  extendIx f (Stuff c)         = f c
  extendIx _ Clear             = Clear
  extendIx f (Hor w1 b1 w2 b2) = Hor w1 (extendIx f b1) w2 (extendIx f b2)
  extendIx f (Ver h1 b1 h2 b2) = Ver h1 (extendIx f b1) h2 (extendIx f b2)

-- 6.3: Juxtaposition ----------------------------------------------------------

-- Máximo de dos Nat promovidos
type family Max (m :: Nat) (n :: Nat) :: Nat
type instance Max 'Z      n       = n
type instance Max ('S m)  'Z      = 'S m
type instance Max ('S m)  ('S n)  = 'S (Max m n)

juxH :: Size '(w1, h1) -> Size '(w2, h2) ->
          Box p '(w1, h1) -> Box p '(w2, h2) ->
            Box p '(w1 :+ w2, Max h1 h2)

-- 6.4: Pain -------------------------------------------------------------------

-- Con esta definición, juxH no puede deducir que la caja resultado tiene como
-- altura el máximo de las alturas de las cajas que procesa.
-- juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
--   case cmp h1 h2 of
--     LTNat n -> Hor w1 (Ver h1 b1 (Sy n) Clear) w2 b2  -- (×)
--     EQNat   -> Hor w1 b1 w2 b2                        -- (×)
--     GTNat n -> Hor w1 b1 w2 (Ver h2 b2 (Sy n) Clear)  -- (×)

-- Solución 1: codificar lemas
-- ∀x 1 ... x n .Natty x 1 → ... → Natty x n → ((l ∼ r ) ⇒ t) → t
maxLT :: forall m z t.Natty m -> Natty z ->
            ((Max m (m :+ 'S z) ~ (m :+ 'S z)) => t) -> t
maxLT Zy      _ t = t
maxLT (Sy m)  z t = maxLT m z t

maxEQ :: forall m t.Natty m -> ((Max m m ~ m) => t) -> t
maxEQ Zy      t = t
maxEQ (Sy m)  t = maxEQ m t

maxGT :: forall n z t.Natty n -> Natty z ->
            ((Max (n :+ 'S z) n ~ (n :+ 'S z)) => t) -> t
maxGT Zy      _ t = t
maxGT (Sy n)  z t = maxGT n z t

juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
  case cmp h1 h2 of
    LTNat z -> maxLT h1 z $ Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
    EQNat   -> maxEQ h1   $ Hor w1 b1 w2 b2
    GTNat z -> maxGT h2 z $ Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)

-- 6.5: Pleasure ---------------------------------------------------------------

-- Solución 2: evitar definir lemas explícitamente. Se redefine Cmp, para
-- que, además de realizar la comparación analizando la diferencia, se
-- pide la prueba del máximo entre ellos.
-- (modificado más adelante).
-- data Cmp :: Nat -> Nat -> * where
--   LTNat :: ((m :+ 'S z) ~ n,  Max m n ~ n) => Natty z -> Cmp m n
--   EQNat :: (m ~ n,            Max m n ~ m) =>            Cmp m n
--   GTNat :: (m ~ (n :+ 'S z),  Max m n ~ m) => Natty z -> Cmp m n

-- Ahora, la definición anterior de juxH (la primera, que no typechequeaba)
-- funciona sin ningun cambio (salvo usar Cmppp en lugar de Cmp).
juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
  case cmp h1 h2 of
    LTNat n -> Hor w1 (Ver h1 b1 (Sy n) Clear) w2 b2
    EQNat   -> Hor w1 b1 w2 b2
    GTNat n -> Hor w1 b1 w2 (Ver h2 b2 (Sy n) Clear)

juxV :: Size '(w1, h1) -> Size '(w2, h2) ->
          Box p '(w1, h1) -> Box p '(w2, h2) ->
            Box p '(Max w1 w2, h1 :+ h2)
juxV (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
  case cmp w1 w2 of
    LTNat n -> Ver h1 (Hor w1 b1 (Sy n) Clear) h2 b2
    EQNat   -> Ver h1 b1 h2 b2
    GTNat n -> Ver h1 b1 h2 (Hor w2 b2 (Sy n) Clear)

-- 6.6: Cutting ----------------------------------------------------------------

-- Para cortar cajas
class Cut (p :: (Nat, Nat) -> *) where
  horCut :: Natty m -> Natty n ->
              p '(m :+ n, h) -> (p '(m, h), p '(n, h))
  verCut :: Natty m -> Natty n ->
              p '(w, m :+ n) -> (p '(w, m), p '(w, n))

-- Comparación para cortar horizontalmente cajas que son la composición
-- horizontal de otras dos cajas.
data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: (b ~ ('S z :+ d), c ~ (a :+ 'S z)) =>
    Natty z ->  CmpCuts a b c d
  EQCuts :: (a ~ c, b ~ d) =>
                CmpCuts a b c d
  GTCuts :: (a ~ (c :+ 'S z), d ~ ('S z :+ b)) =>
    Natty z ->  CmpCuts a b c d

-- Se define una función que realiza la comparación, aprovechando que CmpCuts
-- hace implícitamente las pruebas.
cmpCuts :: ((a :+ b) ~ (c :+ d)) =>
  Natty a -> Natty b -> Natty c -> Natty d -> CmpCuts a b c d
cmpCuts Zy      _ Zy      _ = EQCuts
cmpCuts Zy      _ (Sy c)  _ = LTCuts c
cmpCuts (Sy a)  _ Zy      _ = GTCuts a
cmpCuts (Sy a)  b (Sy c)  d = case cmpCuts a b c d of
  LTCuts z -> LTCuts z
  EQCuts   -> EQCuts
  GTCuts z -> GTCuts z

-- Ahora, se definen los cortes para las cajas
instance Cut p => Cut (Box p) where
  horCut m n (Stuff p) = (Stuff p1, Stuff p2)
    where (p1, p2) = horCut m n p
  horCut _ _ Clear = (Clear, Clear)
  horCut m n (Hor w1 b1 w2 b2) =
    case cmpCuts m n w1 w2 of
      LTCuts z  ->  let (b11, b12) = horCut m (Sy z) b1
                    in (b11, Hor (Sy z) b12 w2 b2)
      EQCuts    ->  (b1, b2)
      GTCuts z  ->  let (b21, b22) = horCut (Sy z) n b2
                    in (Hor w1 b1 (Sy z) b21, b22)
  horCut m n (Ver h1 b1 h2 b2) =
    (Ver h1 b11 h2 b21, Ver h1 b12 h2 b22)
    where (b11, b12) = horCut m n b1
          (b21, b22) = horCut m n b2

  verCut m n (Stuff p) = (Stuff p1, Stuff p2)
    where (p1, p2) = verCut m n p
  verCut _ _ Clear = (Clear, Clear)
  verCut m n (Hor w1 b1 w2 b2) =
    (Hor w1 b11 w2 b21, Hor w1 b12 w2 b22)
    where (b11, b12) = verCut m n b1
          (b21, b22) = verCut m n b2
  verCut m n (Ver h1 b1 h2 b2) =
    case cmpCuts m n h1 h2 of
      LTCuts z -> let (b11, b12) = verCut m (Sy z) b1
                  in (b11, Ver (Sy z) b12 h2 b2)
      EQCuts   -> (b1, b2)
      GTCuts z -> let (b21, b22) = verCut (Sy z) n b2
                  in (Ver h1 b1 (Sy z) b21, b22)

-- 6.7: Boxes as Monoids -------------------------------------------------------

-- Las cajas tienen estructura de Monoide
instance Cut p => Monoid (Box p wh) where
  mempty = Clear

  mappend b Clear               = b
  mappend Clear b'              = b'
  mappend b@(Stuff _) _         = b
  mappend (Hor w1 b1 w2 b2) b'  = Hor w1 (mappend b1 b1') w2 (mappend b2 b2')
    where (b1', b2') = horCut w1 w2 b'
  mappend (Ver h1 b1 h2 b2) b'  = Ver h1 (mappend b1 b1') h2 (mappend b2 b2')
    where (b1', b2') = verCut h1 h2 b'

-- 6.8: Cropping = Clipping + Fitting ------------------------------------------

-- Representa un punto dentro de la caja.
-- (Zy, Zy) es la esquina superior izquierda, contando de abajo hacia arriba y
-- de izquierda a derecha.
type Point = Natty :**: Natty

-- Representa una región dentro de una caja.
-- Se indica mediante la posición de su esquina superior izquierda y su tamaño.
type Region = Point :**: Size

-- Resta type level
type family (m :: Nat) :- (n :: Nat) :: Nat
type instance 'Z    :-  n   = 'Z
type instance 'S m  :- 'Z   = 'S m
type instance 'S m  :- 'S n = m :- n

data Cmp :: Nat -> Nat -> * where
  LTNat :: ((m :+ 'S z) ~ n,  Max m n ~ n, m :- n ~ 'Z)   => Natty z -> Cmp m n
  EQNat :: (m ~ n,            Max m n ~ m, m :- n ~ 'Z)   =>            Cmp m n
  GTNat :: (m ~ (n :+ 'S z),  Max m n ~ m, m :- n ~ 'S z) => Natty z -> Cmp m n

-- Se refleja la resta type level :- en la resta /-/ a nivel de Singletons
(/-/) :: Natty m -> Natty n -> Natty (m :- n)
Zy    /-/ _     = Zy
Sy m  /-/ Zy    = Sy m
Sy m  /-/ Sy n  = m /-/ n

-- En general, se debe definir las operaciones sobre naturales tre veces:
-- * para valores Nat
-- * para tipos Nat
-- * para valores Natty
-- La librería *singletons* puede ayudar con esto.

-- Descartar todo lo que se encuentra a la izquierda y arriba del punto (extraer
-- una región).
clip :: Cut p => Size '(w, h) -> Point '(x, y) ->
  Box p '(w, h) -> Box p '(w :- x, h :- y)
clip (w :&&: h) (x :&&: y) b =
  clipV (w /-/ x :&&: h) y (clipH (w :&&: h) x b)

clipH :: Cut p => Size '(w, h) -> Natty x ->
  Box p '(w, h) -> Box p '(w :- x, h)
clipH (w :&&: _) x b = case cmp w x of
  GTNat d -> snd (horCut x (Sy d) b)
  _       -> Clear

clipV :: Cut p => Size '(w, h) -> Natty y ->
  Box p '(w, h) -> Box p '(w, h :- y)
clipV (_ :&&: h) y b = case cmp h y of
  GTNat d -> snd (verCut y (Sy d) b)
  _       -> Clear

-- Ajustar una caja al tamaño dado. Primero se ajusta horizontalmente, luego
-- verticalmente. Los espacios se completan con Clear.
fit :: Cut p => Size '(w1, h1) -> Size '(w2, h2) ->
  Box p '(w1, h1) -> Box p '(w2, h2)
fit (w1 :&&: h1) (w2 :&&: h2) b = fitV h1 h2 (fitH w1 w2 b)

fitH :: Cut p => Natty w1 -> Natty w2 ->
  Box p '(w1, h) -> Box p '(w2, h)
fitH w1 w2 b = case cmp w1 w2 of
  LTNat d -> Hor w1 b (Sy d) Clear
  EQNat   -> b
  GTNat d -> fst (horCut w2 (Sy d) b)

fitV :: Cut p => Natty h1 -> Natty h2 ->
  Box p '(w, h1) -> Box p '(w, h2)
fitV h1 h2 b = case cmp h1 h2 of
  LTNat d -> Ver h1 b (Sy d) Clear
  EQNat   -> b
  GTNat d -> fst (verCut h2 (Sy d) b)

-- Se implementa crop como una composición de cut y fit.
-- crop :: Cut p => Region '('(x, y), '(w, h)) -> Size '(s, t) ->
--   Box p '(s, t) -> Box p '(w, h)
-- crop ((x :&&: y) :&&: (w :&&: h)) (s :&&: t) b =
--   fit ((s /-/ x) :&&: (t /-/ y)) (w ::&&: h) (clip (s :&&: t) (x :&&: y) b)

-- Capítulo 7: An Editor #######################################################
-- Se implementa un editor de texto como un buffer de cajas con tamaño indexado
-- (Boxes). [El tipo de] La función crop garantiza que las cajas son bien
-- formadas en cuanto a su tamaño.
-- Se manejan valores dinámicos que provienen del mundo real, convirtiéndolos
-- a su equivalente puro de tamaño indexado mediante existenciales.

-- 7.1 Character boxes ---------------------------------------------------------

type CharMatrix = Matrix Char
type CharBox    = Box CharMatrix

-- Llenar una matrix con el mismo caracter.
matrixChar :: Char -> Size wh -> CharMatrix wh
matrixChar c (w :&&: h) = Mat (vcopies h (vcopies w c))

renderCharBox :: Size wh -> CharBox wh -> CharMatrix wh
renderCharBox _ (Stuff css) = css
renderCharBox wh Clear = matrixChar ' ' wh
renderCharBox (w :&&: _) (Ver h1 b1 h2 b2) =
  Mat (unMat (renderCharBox (w :&&: h1) b1)
    `vappend` unMat (renderCharBox (w :&&: h2) b2))
-- En lugar de utilizar la interfaz de Applicative, se utiliza vcopies h para
-- pure y vapp para (<*>), de modo de evitar el overhead de apelar a natter h
renderCharBox (_ :&&: h) (Hor w1 b1 w2 b2) =
  Mat (vcopies h vappend
    `vapp` unMat (renderCharBox (w1 :&&: h) b1)
    `vapp` unMat (renderCharBox (w2 :&&: h) b2))

-- Desplegar una matriz de caracteres como una lista de strings.
stringOfCharMatrix :: CharMatrix wh -> [String]
stringOfCharMatrix (Mat vs) = foldMap ((:[]) . foldMap (:[])) vs

-- Para hacer cut (y por lo tanto crop) de cajas con contenido matricial,
-- se instancia la type class Cut para matrices.
instance Cut (Matrix e) where
  horCut m _ (Mat ess) =
    (Mat (fst <$> ps), Mat (snd <$> ps)) where
      ps = vchop m <$> ess
  verCut m _ (Mat ess) = (Mat tess, Mat bess) where
    (tess, bess) = vchop m ess

-- 7.2 Existentials ------------------------------------------------------------

wrapPair :: (a -> Ex p) -> (b -> Ex q) -> (a, b) -> Ex (p :**: q)
wrapPair w1 w2 (x1, x2) = case (w1 x1, w2 x2) of
  (Ex v1, Ex v2) -> Ex (v1 :&&: v2)

type WPoint = Ex Point
type WSize = Ex Size
type WRegion = Ex Region

intToNat :: Int -> Nat
intToNat 0 = Z
intToNat n = S (intToNat (n - 1))

wrapInt :: Int -> WNat
wrapInt = wrapNat . intToNat
wrapPoint :: (Int, Int) -> Ex (Natty :**: Natty)
wrapPoint = wrapPair wrapInt wrapInt
wrapSize :: (Int, Int) -> Ex (Natty :**: Natty)
wrapSize = wrapPair wrapInt wrapInt
wrapRegion :: ((Int, Int), (Int, Int))
                -> Ex ((Natty :**: Natty) :**: (Natty :**: Natty))
wrapRegion = wrapPair wrapPoint wrapSize

newtype Flip f a b = Flip { unFlip :: f b a }

type WVec a = Ex (Flip Vec a)

wrapVec :: [a] -> WVec a
wrapVec []      = Ex (Flip V0)
wrapVec (x:xs)  = case wrapVec xs of
  Ex (Flip v) -> Ex (Flip (x :> v))

type WLenVec a = Ex (Natty :*: Flip Vec a)

wrapLenVec :: [a] -> WLenVec a
wrapLenVec []     = Ex (Zy :&: Flip V0)
wrapLenVec (x:xs) = case wrapLenVec xs of
  Ex (n :&: Flip v) -> Ex (Sy n :&: Flip (x :> v))

type WSizeCharBox = Ex (Size :*: CharBox)

-- Los strings de largo w se piensan como CharBoxes de tamaño (w, 1).
wrapString :: String -> WSizeCharBox
wrapString s = case wrapLenVec s of
  Ex (n :&: Flip v) -> Ex ((n :&&: Sy Zy) :&: Stuff (Mat (pure v)))

-- Ahora se hace lo mismo pero con listas de h strings.
wrapStrings :: [String] -> WSizeCharBox
wrapStrings []      = Ex ((Zy :&&: Zy) :&: Clear)
wrapStrings (s:ss)  =
  case (wrapString s, wrapStrings ss) of
    (Ex ((w1 :&&: h1) :&: b1), Ex ((w2 :&&: h2) :&: b2)) ->
      Ex (((w1 `maxn` w2) :&&: (h1 /+/ h2)) :&: juxV (w1 :&&: h1) (w2 :&&: h2) b1 b2)

-- Máximo en naturales Singleton.
maxn :: Natty m -> Natty n -> Natty (Max m n)
maxn Zy     n       = n
maxn(Sy m)  Zy      = Sy m
maxn (Sy m) (Sy n)  = Sy (maxn m n)

-- Suma en naturales Singleton.
(/+/) :: Natty m -> Natty n -> Natty (m :+ n)
Zy      /+/ n = n
(Sy m)  /+/ n = Sy (m /+/ n)

-- 7.2 Cursors -----------------------------------------------------------------

-- Un cursor es una tripleta:
-- (elementos previos, elemento actual, elementos siguientes).
type Cursor a m = ([a], m, [a])

type StringCursor = Cursor Char ()

type TextCursor = Cursor String StringCursor

deactivate :: Cursor a () -> (Int, [a])
deactivate = outward 0
  where
    outward i ([], (), xs)      = (i, xs)
    outward i (x:xz, (), xs)  = outward (i+1) (xz, (),x:xs)

activate :: (Int, [a]) -> Cursor a ()
activate (i, xs) = inward i ([], (), xs)
  where
    inward _ c@(_, (), [])  = c
    inward 0 c              = c
    inward i (xz, (), x:xs) = inward (i-1) (x:xz, (), xs)

whatAndWhere :: TextCursor -> (WSizeCharBox, (Int, Int))
whatAndWhere (czz, cur, css) = (wrapStrings strs, (x, y))
  where
    (x, cs)   = deactivate cur
    (y, strs) = deactivate (czz, (), cs:css)

main :: IO ()
main = putStrLn "Hello World"
