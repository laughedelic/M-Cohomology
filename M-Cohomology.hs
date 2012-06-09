{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

import Math.Algebras.VectorSpace hiding (e, e')
import Math.Algebras.Structures
import Data.List
import Data.Monoid
import Data.Functor
import qualified Data.IntMap as M
import Math.LinearAlgebra.Sparse

---------------------------------------------------------------------------
-- Описание группы --
---------------------

-- основные константы задачи
k  = 4           -- M_2^k
r  = 2^(k-2)
rr = 2*r         -- b^2r = 1
t  = r+1         -- ba = ab^t

data G = Element Int Int 
         deriving Eq

element :: Int -> Int -> G
element m n = Element (m `mod` 2) (n `mod` rr)

(.*.) :: G -> G -> G
(Element p l) .*. (Element 0 s) = element  p    (  l+s)
(Element p l) .*. (Element 1 s) = element (p+1) (t*l+s)

e' = Element 0 0
a' = Element 1 0
b' = Element 0 1

instance Ord G where
    (Element m1' n1') <= (Element m2' n2') = 
        (m1 < m2) || ((m1 == m2) && (n1 <= n2))
        where [m1,m2] = map (`mod` 2)  [m1',m2']
              [n1,n2] = map (`mod` rr) [n1',n2']

instance Show G where
    show (Element 0 0) = "1"
    show (Element m 0) = take m "a"
    show (Element m 1) = take m "a" ++ "b"
    show (Element m n) = take m "a" ++ "b" ++ superscript n

digit n = "⁰¹²³⁴⁵⁶⁷⁸⁹"!!(n `mod` 10)
superscript n = let (n',k) = n `divMod` 10 
                in (if n' > 0 then superscript n' else "") ++ [digit k]

_G_ = [ Element m n | m <- [0,1], n <- [0 .. rr-1] ]

---------------------------------------------------------------------------
-- Построение групповой алгебры --
----------------------------------

instance (Eq k, Num k) => Algebra k G where
   -- unit :: k -> Vect k b
      unit 0 = zero
      unit k = V [(e', k)]
   -- mult :: Vect k (Tensor b b) -> Vect k b
      mult (V vs) = nf $ V [(g.*.h, k) | ((g,h), k) <- vs ]

-- простой конструктор: коэффициент * элемент группы
(&) :: (Algebra k G) => k -> G -> Vect k G
z&x = V [(x,z)]

basis = map (1&) _G_

type Z = Integer
-- целочисленная групповая алгебра
type ZG = Vect Z G

-- образующие группы как элементы групповой алгебры
e = 1&e' :: ZG
a = 1&a' :: ZG
b = 1&b' :: ZG

-- из списка 2^k коэффициентов получить элемент гр.алгебры
constr :: (Eq k, Num k, Algebra k G) => [k] -> Vect k G
constr = nf . V . zip _G_

-- наоборот, получить список коэффициентов данного элемента
coeffs ::  Num k => Vect k G -> [k]
coeffs (V x) = [ maybe 0 id (lookup g x) | g <- _G_ ]

sparseCoeffs = sparseList . coeffs

---------------------------------------------------------------------------
-- Описание дифференциалов резольвенты --
-----------------------------------------

_Nb :: ZG
_Nb = sum [ b^i | i <- [0 .. rr-1] ]

_L :: ZG
_L  = sum [ b^i | i <- [0 .. t-1] ]

-- _L*a == a*l
l = a*_L*a

-- стрелки специальной двумерной диаграммы (см. [Wall])
ar :: Int -> Int -> Int -> ZG
                                                                 
ar 0 m n | m < 1 || n < 0 = 0
        | odd  m         = b-1
        | even m         = _Nb
                                                                 
ar 1 m n | m < 0  || n < 1  = 0
        | even m && odd  n =   a*l^m' - 1
        | even m && even n =   a*l^m' + 1 
        where m' = (m `div` 2)
ar 1 m n | odd  m && odd  n =  -a*l^m' + 1
        | odd  m && even n =  -a*l^m' - 1
        where m' = ((m+1) `div` 2)
                                                                 
ar 2 m n | m < 0 || n < 2 = 0
        | even m         = 0
        | odd  m         = fromInteger $ -(t'^(2*m') - 1) `div` rr'
        where m' = ((m+1) `div` 2)
              t' = toInteger t
              rr' = toInteger rr
                                                                 
ar _ _ _ = 0


-- дифференциалы «тотализации»
--
-- δ n : ZGⁿ⁺² → ZGⁿ⁺¹
--
delta' :: Int -> SparseMatrix ZG
delta' n = fromAssocListWithSize (n+1,n+2)
    [ ((i+1,j+1), d_ i j) | j <- [0 .. n+1] 
                          , i <- [0 .. n  ] ]
            where d_ i j  = ar (i-j+1) j (n+1-j)

-- ленивая мемоизация
deltas = map delta' [0 .. ]
δ n = deltas !! n 

-- проверка того, что δ² = 0
checkdd k = isZeroMx (δ k × δ (k+1))

---------------------------------------------------------------------------
-- Применение Hom_ZG(–,Z) --
----------------------------

-- отображение пополнения
ε :: ZG -> Z
ε (V ts) = sum (map snd ts)

-- дифференциалы комлекса Hom_ZG(ZGⁿ,Z) ≃ Zⁿ
-- 
-- dⁿ : Zⁿ⁺¹ → Zⁿ⁺²
--
d :: Int -> SparseMatrix Z
d = trans . fmap ε . δ

---------------------------------------------------------------------------
-- Описание групп когомологий Hⁿ(G,Z) --
----------------------------------------

t' = toInteger t
κ k = (t'^k + 1) `div` 2
γ k = (t'^k - 1) `div` (t'-1)

-- образующие групп когомологий
-- в виде наборов векторов
coHom :: Int -> [SparseVector Z]
coHom 0 = [singVec 1]
coHom m = map fromPairs $ 
    if l == 1 -- m = 2n+2
       then   [(1,1)]
          : [ [(4*i, -(κ i)*(γ i)), (4*i+1, 1)] | i <- [1 .. k] ]
         ++ [ if p == 0 then [(m, -(γ (n+1)))          , (m+1, 2)]
                        else [(m, -(κ (k+1))*(γ (k+1))), (m+1, 1)] ]
       else -- l = 0, m = 2n+1
            [ [(2*i, -(κ i)), (2*i+1, t'-1)] | i <- [2,4 .. n] ]

    where (n,l) = (m-1) `divMod` 2
          (k,p) =  n    `divMod` 2
          fromPairs = foldl' vecIns (zeroVec (m+1))

-- то же самое в виде матриц
coHomMx ::  Int -> SparseMatrix Z
coHomMx = fromRows . coHom

-- j-я образующая i-й группы когомологий
h :: Int -> Int -> SparseVector Z
h i j = coHomMx i `row` j

-- порядки образующих в группе (коэффициенты соотношений)
mods m = twos ++ (if l == 0 then [] 
                            else if p == 0 then [2,2^(k-2)] 
                                           else [2,2^(k-1)])
    where (n,l) = (m-1) `divMod` 2
          (_,p) =  n    `divMod` 2
          twos  = replicate ((m-1) `div` 4) 2

---------------------------------------------------------------------------
-- Решение уравнений в групповой алгебре --
-------------------------------------------

xCoeffs :: ZG -> SparseMatrix Z
xCoeffs x = trans $ sparseMx [ coeffs (x*g) | g <- basis ]

lhs :: SparseMatrix ZG -> SparseMatrix Z
lhs m = sizedBlockSMx (2^k,2^k) (fmap xCoeffs m)

concatVec ::  [SparseVector α] -> SparseVector α
concatVec = foldl' (<>) emptyVec

rhsCoeffs :: ZG -> SparseVector Z
rhsCoeffs kg = sparseCoeffs kg

rhs :: SparseMatrix ZG -> [SparseVector Z]
rhs m = fmap (concatVec . fmap rhsCoeffs) $ fillMx $ trans m

separate :: SparseVector Z -> SparseVector ZG
separate (SV l z) = M.foldlWithKey' add (zeroVec (l `div` (2^k))) z
    where add acc m x = let i = (m-1) `div`(2^k)+ 1
                            j = (m-1) `mod` 2^k
                            kg = x&(_G_!!j)
                        in acc `vecIns` (i, acc!i + kg)

solveZGSystems :: SparseMatrix ZG -> SparseMatrix ZG -> SparseMatrix ZG
solveZGSystems m bs = 
    trans $ fromRows $ fmap separate $ solveLinSystems (lhs m) (rhs bs)

---------------------------------------------------------------------------
-- Трансляции (подъёмы) --
--------------------------

type Translation = SparseMatrix ZG

-- все трансляции данного коцикла
tr :: SparseVector Z -> [Translation]
tr f = selfRec  -- ленивая мемоизация
      where k = dim f - 1
            t0 = fromRows [fmap (&e') f]
            selfRec = t0 : (zipWith ttr [1 .. ] selfRec)
            ttr m prev = solveZGSystems (δ (m-1)) (prev × (δ (k+m-1)))

-- трансляции всех образующих всех групп когомологий
tt :: [[[Translation]]]
tt = map (map tr) $ map coHom [1 .. ]

-- k-я трансляция j-й образующей i-группы когомологий
ττ :: Int -> Int -> Int -> Translation
ττ i j k = tt !! (i-1) !! (j-1) !! k

-- проверка определяющих тождеств для набора трансляций
checkAll :: [Translation] -> [Bool]
checkAll ts = let k  = length ts - 1
                  eq m t1 t0 = (δ (m-1)) × t1 == t0 × (δ (k+m-1))
              in zipWith3 eq [1 .. ] (tail ts) ts 

---------------------------------------------------------------------------
-- cup-произведение --
----------------------

vecDiv' v w = if isZeroVec u then 0 else snd $ M.findMin $ vec $ u
    where u = vecDiv v w
vecDiv = intersectVecsWith div
vecMod = intersectVecsWith mod

-- несколько стадий cup-произведения:

-- по данному коциклу возвращает представитель соотв. когом. класса
cl t = sum $ zipWith (\v k -> (k*)<$>v) basis $ lin t
    where basis = coHom (dim t - 1)

-- представляет коцикл в виде линейной комбинации образующих соотв.
-- группы когомологий и её возвращает коэффициенты
lin t = zipWith mod (map (vecDiv' t) basis) (mods (dim t - 1))
    where basis = coHom (dim t - 1)

-- cup-произведение двух образующих соотв. групп когомологий
(m,i) ‿ (n,j) | m <= n = cl $ (ε <$> (ττ m i 0) × (ττ n j m)) `row` 1
              | otherwise = ((-1)^(m+n)*) <$> (n,j) ‿ (m,i)
cup = (‿)

-- соотношения между образующими n-й и m-й групп
relations m n = putStrLn $ unlines
    [ row i j | i <- [1 .. length (coHom m)]
              , j <- [1 .. length (coHom n)] ]
    where row i j = concat [show (m,i)," ‿ ",show (n,j)," = ", right i j]
          right i j = let result = filter ((0/=) . fst) 
                                 $ zip (lin $ (m,i) ‿ (n,j)) 
                                       [ (m+n, k) | k <- [1 .. ] ]
                      in if null result then "0"
                            else intercalate " + " $ map show' result
          show' (0,_) = ""
          show' (1,x) = show x
          show' (k,x) = show k ++ "·" ++ show x

-- представление образующих n-й группы через образующие меньшей степени
representation n = sequence_ [ relations i (n-i) | i <- [1 .. n `div` 2] ]
