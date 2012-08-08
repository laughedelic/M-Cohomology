
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
-- Group description --
-----------------------

-- main constants
k  = 4           -- M_2^k
r  = 2^(k-2)
rr = 2*r         -- b^2r = 1
t  = r+1         -- ba = ab^t

data G = Element Int Int 
         deriving Eq

-- constructor of elements with respect to it's order
element :: Int -> Int -> G
element m n = Element (m `mod` 2) (n `mod` rr)

-- multiplication in group
(.*.) :: G -> G -> G
(Element p l) .*. (Element 0 s) = element  p    (  l+s)
(Element p l) .*. (Element 1 s) = element (p+1) (t*l+s)

e' = Element 0 0 :: G
a' = Element 1 0 :: G
b' = Element 0 1 :: G

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

digit n = "⁰¹²³⁴⁵⁶⁷⁸⁹" !! (n `mod` 10)
superscript n = let (n',k) = n `divMod` 10 
                in (if n' > 0 then superscript n' else "") ++ [digit k]

-- list of group elements
_G_ = [ Element m n | m <- [0,1], n <- [0 .. rr-1] ]

---------------------------------------------------------------------------
-- Construction of group algebra --
-----------------------------------

instance (Eq k, Num k) => Algebra k G where
   -- unit :: k -> Vect k b
      unit 0 = zero
      unit k = V [(e', k)]
   -- mult :: Vect k (Tensor b b) -> Vect k b
      mult (V vs) = nf $ V [(g.*.h, k) | ((g,h), k) <- vs ]

-- simple constructor: coefficient * group element
(&) :: (Algebra k G) => k -> G -> Vect k G
z&x = V [(x,z)]

basis = map (1&) _G_

type Z = Integer
-- integral group algebra
type ZG = Vect Z G

-- group basis as elements of group algebra
e = 1&e' :: ZG
a = 1&a' :: ZG
b = 1&b' :: ZG

-- obtains an element of group algebra from a list of 2^k coefficients
constr :: (Eq k, Num k, Algebra k G) => [k] -> Vect k G
constr = nf . V . zip _G_

-- opposite: gives element's coefficient list
coeffs ::  Num k => Vect k G -> [k]
coeffs (V x) = [ maybe 0 id (lookup g x) | g <- _G_ ]

-- same as a sparse list
sparseCoeffs = sparseList . coeffs

---------------------------------------------------------------------------
-- Description of resolutions differentials --
----------------------------------------------

_Nb :: ZG
_Nb = sum [ b^i | i <- [0 .. rr-1] ]

_L :: ZG
_L  = sum [ b^i | i <- [0 .. t-1] ]

-- _L*a == a*l
l = a*_L*a

-- arrows of the special two-dimentional diagram from [Wall]
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


-- differentials of "totalisation"
--
-- δ n : ZGⁿ⁺² → ZGⁿ⁺¹
--
δ' :: Int -> SparseMatrix ZG
δ' n = fromAssocListWithSize (n+1,n+2)
    [ ((i+1,j+1), d_ i j) | j <- [0 .. n+1] 
                          , i <- [0 .. n  ] ]
            where d_ i j  = ar (i-j+1) j (n-j+1)

-- lazy memoisation
deltas = map δ' [0 .. ]
δ n = deltas !! n 

-- checks that δ² = 0
checkdd k = isZeroMx (δ k × δ (k+1))

ε :: ZG -> Z
ε (V ts) = sum (map snd ts)

-- differentials of the Hom_ZG(ZGⁿ,Z) ≃ Zⁿ complex
-- 
-- dⁿ : Zⁿ⁺¹ → Zⁿ⁺²
--
d :: Int -> SparseMatrix Z
d = trans . fmap ε . δ

---------------------------------------------------------------------------
-- Description of the Hⁿ(G,Z) cohomology groups --
--------------------------------------------------

t' = toInteger t
κ k = (t'^k + 1) `div` 2
γ k = (t'^k - 1) `div` (t'-1)

-- cohomology groups generators
-- as lists of vectors
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

-- same as sparse matrices
coHomMx ::  Int -> SparseMatrix Z
coHomMx = fromRows . coHom

-- j-th generator of i-th cohomology group
h :: Int -> Int -> SparseVector Z
h i j = coHomMx i `row` j

-- orders of groups generators (coefficients of relations)
mods m = twos ++ (if l == 0 then [] 
                            else if p == 0 then [2,2^(k-2)] 
                                           else [2,2^(k-1)])
    where (n,l) = (m-1) `divMod` 2
          (_,p) =  n    `divMod` 2
          twos  = replicate ((m-1) `div` 4) 2

---------------------------------------------------------------------------
-- Solving equations in the group algebra --
--------------------------------------------

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
    where add acc m x = let i  = (m-1) `div`(2^k)+ 1
                            j  = (m-1) `mod` 2^k
                            kg = x&(_G_!!j)
                        in acc `vecIns` (i, acc!i + kg)

solveZGSystems :: SparseMatrix ZG -> SparseMatrix ZG -> SparseMatrix ZG
solveZGSystems m bs = 
    trans $ fromRows $ fmap separate $ solveLinSystems (lhs m) (rhs bs)

---------------------------------------------------------------------------
-- Translations (cocycles lifting) --
-------------------------------------

type Translation = SparseMatrix ZG

-- all translations of given cocycle
tr :: SparseVector Z -> [Translation]
tr f = selfRec  -- ленивая мемоизация
      where k = dim f - 1
            t0 = fromRows [fmap (&e') f]
            selfRec = t0 : (zipWith ttr [1 .. ] selfRec)
            ttr m prev = solveZGSystems (δ (m-1)) (prev × (δ (k+m-1)))

-- translations of all generators of all cohomology groups
tt :: [[[Translation]]]
tt = map (map tr) $ map coHom [1 .. ]

-- k-th translation of j-th generator of i-th cohomology group
ττ :: Int -> Int -> Int -> Translation
ττ i j k = tt !! (i-1) !! (j-1) !! k

-- check of the definition equations for translations set
checkAll :: [Translation] -> [Bool]
checkAll ts = let k  = length ts - 1
                  eq m t1 t0 = (δ (m-1)) × t1 == t0 × (δ (k+m-1))
              in zipWith3 eq [1 .. ] (tail ts) ts 

---------------------------------------------------------------------------
-- cup-production --
--------------------

vecDiv' v w = if isZeroVec u then 0 else snd $ M.findMin $ vec $ u
    where u = intersectVecsWith div v w

-- returns a representative of the cohomology class that 
-- corresponds to the given cocycle
cl t = sum $ zipWith (\v k -> (k*)<$>v) basis $ lin t
    where basis = coHom (dim t - 1)

-- represents cocycle as a linear combination of generators of the
-- corresponding cohomology group and returns it's coefficients list
lin t = zipWith mod (map (vecDiv' t) basis) (mods (dim t - 1))
    where basis = coHom (dim t - 1)

-- cup-production of the i-th generator of m-th group by the j-th generator of n-th group
(m,i) ‿ (n,j) | m <= n    = cl $ (ε <$> (ττ m i 0) × (ττ n j m)) `row` 1
              | otherwise = ((-1)^(m+n)*) <$> (n,j) ‿ (m,i)
cup = (‿)

-- relations between generators of the n-th and m-th groups
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

-- representation of generators of n-th group using generators of lower degree
representation n = sequence_ [ relations i (n-i) | i <- [1 .. n `div` 2] ]

