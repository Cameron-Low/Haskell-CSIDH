{-# LANGUAGE KindSignatures, DataKinds #-}
module Main where

import System.Random (randomRIO)
import Data.Bits (testBit)
import Math.NumberTheory.Logarithms (integerLog2')
import Math.NumberTheory.Moduli.Sqrt
import Math.NumberTheory.Roots (integerSquareRoot)
import Crypto.Number.ModArithmetic (expFast, inverseCoprimes)

{- HELPERS -}

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
    | n == 0 = newVal:xs
    | otherwise = x:replaceNth (n-1) newVal xs

-- Calculate the bit length of an arbitraryly sized integer
bits :: Integer -> Int
bits 0 = 1
bits x = integerLog2' x + 1


{- MONTGOMERY CURVE POINT ARITHMETIC -}

-- A projectivised x-line montogomery curve point 
type Point = (Integer, Integer)

point_eq :: Point -> Point -> Integer -> Bool
point_eq (px, pz) (qx, qz) p = ((px * qz) `mod` p) == ((qx * pz) `mod` p)

-- A mongomery curve with coefficient and prime
type Curve = (Point, Integer, Integer)  

pre_comp :: Curve -> Curve
pre_comp ((a, c), _, p) = ((a, c), a2c4, p)
    where
        c2 = (c + c) `mod` p
        a2c = (a + c2) `mod` p
        a2c4 = (a2c * inv4) `mod` p

-- x-line point duplication for montgomery curves
-- Args: P, curve
-- Return [2]P
mont_dup :: Point -> Curve -> Point
mont_dup (_, 0) _ = (0, 0)
mont_dup (x, z) ((a, c), a2c4, p) = (x', z')
    where
        xpz = (x + z) `mod` p
        xmz = (x - z) `mod` p
        xpz2 = expFast xpz 2 p
        xmz2 = expFast xmz 2 p
        cxmz2 = (c * xmz2) `mod` p
        xz4 = (xpz2 - xmz2) `mod` p
        x' = (cxmz2 * xpz2) `mod` p
        z' = (xz4 * (cxmz2 + a2c4 * xz4)) `mod` p

-- x-line differential point addition for montgomery curves
-- Args: P, Q, P-Q, curve
-- Return: P + Q
mont_diff_add :: Point -> Point -> Point -> Curve -> Point
mont_diff_add (0, 0) _ _ _ = (0, 0)
mont_diff_add _ (0, 0) _ _ = (0, 0)
mont_diff_add _ _ (0, _) _ = (0, 0)
mont_diff_add _ _ (_, 0) _ = (0, 0)
mont_diff_add (x1, z1) (x2, z2) (x3, z3) (_, _, p) = (x4, z4)
    where
        xpz1 = (x1 + z1) `mod` p
        xmz1 = (x1 - z1) `mod` p
        xpz2 = (x2 + z2) `mod` p
        xmz2 = (x2 - z2) `mod` p
        lmul = (xmz1 * xpz2) `mod` p
        rmul = (xpz1 * xmz2) `mod` p

        x4 = (z3 * expFast (lmul + rmul) 2 p) `mod` p
        z4 = (x3 * expFast (lmul - rmul) 2 p) `mod` p

mont_ladder :: Integer -> Point -> Curve -> Point
mont_ladder 0 _ _ = (0, 0)
mont_ladder k q (cf, a2c4, p) = loop q (mont_dup q c) (bits k - 2)
                            where
                                c = (cf, a2c4, p)
                                loop :: Point -> Point -> Int -> Point
                                loop r0 r1 (-1) = r0 
                                loop r0 r1 i
                                    | testBit k i = loop diff (mont_dup r1 c) (i-1)
                                    | otherwise = loop (mont_dup r0 c) diff (i-1)
                                        where
                                            diff = mont_diff_add r0 r1 (normalize q p) c

-- Test if a point is on the given curve
on_curve :: Integer -> Curve -> Int
on_curve x ((a,c), a2c4, p) = if jacobi val p /= MinusOne then 1 else -1
    where
        cx = (c * x) `mod` p
        cx2 = (cx * x) `mod` p
        ax = (a * x) `mod` p
        axc = (ax + c) `mod` p
        brak = (cx2 + axc) `mod` p
        val = (cx * brak) `mod` p
        
-- Convert the projectivised x coord to just an affine form
normalize :: Point -> Integer -> Point
normalize (x, 1) _ = (x, 1)
normalize (_, 0) _ = (1, 0)
normalize (x, z) p = ((x * inverseCoprimes z p) `mod` p, 1) 


{- ISOGENY COMPUTATION -}

-- Args: isogeny degree, kernel generator, point, domain curve
renes_velu :: Integer -> Point -> Point -> Curve -> (Point, Curve)
renes_velu l (tx, tz) (qx, qz) ((a, c), a2c4, p)
    | l == 3 = (ppoint, (calc_coeff (pix, piz), 0, p))
    | otherwise = (ppoint', (calc_coeff (pix', piz'), 0, p))
    where
        -- Synonyms
        curve = ((a, c), a2c4, p)
        tor_gen = (tx, tz)

        -- Calculate the case l = 3
        (pix, piz) = ((tx - tz) `mod` p, (tx + tz) `mod` p)
        t1 = (tx * qx - tz * qz) `mod` p
        t2 = (tz * qx - tx * qz ) `mod` p
        ppoint = ((qx * expFast t1 2 p) `mod` p, (qz * expFast t2 2 p) `mod` p)

        -- Pre-compute the first step of the loop to get around the differential addition incompleteness
        q_diffs = ((qx - qz) `mod` p, (qx + qz) `mod` p)
        double = mont_dup tor_gen curve
        pre_comp_step_1 = push ((pix, piz), (t1, t2)) q_diffs double curve

        -- Perform the rest of the loop
        ((pix', piz'), (ppx, ppz)) = renes_loop ((l-1) `div` 2 - 2) pre_comp_step_1 q_diffs tor_gen tor_gen double curve
        
        -- Calculate the image of the point under the calculated l-isogeny
        ppoint' = ((qx * expFast ppx 2 p) `mod` p, (qz * expFast ppz 2 p) `mod` p)

        -- Use Moody-Shumow formulae for computing coefficient
        calc_coeff :: Point -> Point
        calc_coeff (xp, zp) = (a', c')
            where
                pix2 = expFast xp 2 p
                pix4 = expFast pix2 2 p
                pix8 = expFast pix4 2 p
                piz2 = expFast zp 2 p
                piz4 = expFast piz2 2 p
                piz8 = expFast piz4 2 p
                a2c4l = expFast a2c4 l p
                am2c4l = expFast ((a2c4 - c) `mod` p) l p
                ea = (piz8 * a2c4l) `mod` p 
                ed = (pix8 * am2c4l) `mod` p 
                a' = (2 * ((ea + ed) `mod` p)) `mod` p
                c' = (ea - ed) `mod` p


-- Args: iterations, summation vals, point diffs, previous torsion point, torsion generator, current torsion point, curve
renes_loop :: Integer -> ((Integer, Integer), Point) -> Point -> Point -> Point -> Point -> Curve -> ((Integer, Integer), Point)
renes_loop 0 vals _ _ _ _ _ = vals
renes_loop k vals qd prev_tor_p tor_p cur_tor_p c = renes_loop (k-1) (push vals qd new_tor_p c) qd cur_tor_p tor_p new_tor_p c
    where new_tor_p = mont_diff_add tor_p cur_tor_p prev_tor_p c

push :: (Point, Point) -> Point -> Point -> Curve -> (Point, Point)
push ((pix, piz), (pqx, pqz)) (xmz, xpz) (tx, tz) (cf, a2c4, p) = ((pix', piz'), (pqx', pqz'))
    where
        txmz = (tx - tz) `mod` p
        txpz = (tx + tz) `mod` p
        lmul = (xmz * txpz) `mod` p
        rmul = (xpz * txmz) `mod` p

        pix' = (pix * txmz) `mod` p
        piz' = (piz * txpz) `mod` p
        pqx' = (pqx * (lmul + rmul) `mod` p) `mod` p
        pqz' = (pqz * (lmul - rmul) `mod` p) `mod` p


{- Velusqrt -}

compute_kernel :: Point -> Integer -> Curve -> [Point]
compute_kernel gen 1 _ = [gen]
compute_kernel gen ord (cf, a2c4, p) = [gen, double] ++ (loop gen double (bits ord - 2))
                            where
                                c = (cf, a2c4, p)
                                double = mont_dup gen c

                                loop :: Point -> Point -> Int -> [Point]
                                loop r0 r1 (-1) = [r0] 
                                loop r0 r1 i
                                    | testBit ord i = diff : (loop diff (mont_dup r1 c) (i-1))
                                    | otherwise = dup : (loop dup diff (i-1))
                                        where
                                            diff = mont_diff_add r0 r1 (normalize gen p) c
                                            dup = mont_dup r0 c


compute_index_sets :: Int -> ([Int], [Int], [Int])
compute_index_sets l = if b /= 0 then (i, j, k) else ([], [], k)
    where
        l' = l - 1
        b = (integerSquareRoot l') `div` 2
        b' = if b == 0 then 0 else l' `div` (4 * b)
        j = [2 * k + 1 | k <- [0..(b - 1)]] 
        i = [(2 * b) * (2 * k + 1) | k <- [0..(b' - 1)]]
        k_start = 4 * b * b' + 1
        k = [k_start, (k_start + 2)..l']


{- PUBLIC KEY GENERATION -}

-- Calculate the indices of the factors we will use for this point
get_indices :: [Int] -> Int -> [Int]
get_indices sk dir = [i | i <- [0..73], (sk !! i) * dir > 0] 

-- Calculate the scalar point for multiplication given the list of factors for a given direction
calc_k :: [Int] -> Integer
calc_k = foldr op 1
    where
        op :: Int -> Integer -> Integer
        op i x = x * (factors !! i)

-- Check if we have any non-zero exponents left
all_zero :: [Int] -> Bool
all_zero [] = True
all_zero (x:xs)
    | x /= 0 = False
    | otherwise = all_zero xs

twist :: Curve -> Curve
twist ((a, c), a2c4, p) = pre_comp ((p - a, c), a2c4, p)

-- Args: Secret key, direction, factors that correspond to the direction, scalar for point multiplication, an image point, domain curve
act_with_ells :: [Int] -> Int -> [Int] -> Integer -> Point -> Curve -> ([Int], Curve)
act_with_ells sk _ [] _ _ c = (sk, c)
act_with_ells sk _ _ _ (qx, 0) c = (sk, c)
act_with_ells sk dir (x:xs) k q (cf, a2c4, p) = if tpz /= 0 then act_with_ells sk' dir xs k' new_q (pre_comp new_curve) else act_with_ells sk dir xs k q curve
    where
        curve = (cf, a2c4, p)
        ell = factors !! x
        k' = k `div` ell
        (tpx, tpz) = mont_ladder k' q curve
        (new_q, new_curve) = renes_velu ell (tpx, tpz) q curve
        sk' = replaceNth x ((sk !! x) - dir) sk

gen_pub_key :: ([Int], Curve) -> IO Curve
gen_pub_key (sk, (cf, a2c4, p))
    | all_zero sk = return (cf, a2c4, p)
    | otherwise = do
        point <- randomRIO(1, p - 1)
        gen_pub_key (gen_pub_key_loop sk point (cf, a2c4, p))

gen_pub_key_loop :: [Int] -> Integer -> Curve -> ([Int], Curve)
gen_pub_key_loop sk point ((a, c), a2c4, p) = if indices == [] then (sk, in_curve) else (sk', new_curve)
    where
        in_curve = ((a, c), a2c4, p) 
        dir = on_curve point in_curve
        curve = if dir == -1 then twist in_curve else in_curve
        indices = get_indices sk dir
        k = calc_k indices
        q = mont_ladder ((p+1) `div` k) (toInteger dir * point, 1) curve 
        (sk', out_curve) = act_with_ells sk dir indices k q curve
        new_curve = if dir == -1 then twist out_curve else out_curve

{- PRIVATE KEY GENERATION -}

get_rand_list :: Int -> (Int, Int) -> IO ([Int])
get_rand_list 0 _ = return []
get_rand_list n range = do
    x <- randomRIO range
    xs <- get_rand_list (n-1) range
    return (x:xs)

gen_priv_key :: [Int] -> IO ([Int])
--gen_priv_key xs = return (tst xs)
gen_priv_key _ = get_rand_list (length factors) (-5, 5)


{- CSIDH CONSTANTS -}

-- CSIDH factors
factors :: [Integer]
factors = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 587]

-- CSIDH prime
csidh_p :: Integer
csidh_p = 4 * (foldr (*) 1 factors) - 1

-- Inverse 4 mod CSIDH prime
inv4 :: Integer
inv4 = inverseCoprimes 4 csidh_p

-- CSIDH curve
csidh_curve :: Curve
csidh_curve = pre_comp ((0, 100), 1, csidh_p)

-- Random key
tst :: [Int] -> [Int]
tst xs = xs ++ (drop (length xs) [0 | _ <- [1..73]]) ++ [0]

-- Test if the thing works
main :: IO ()
main = do
    skA <- gen_priv_key [-3, -5, 4]
    skB <- gen_priv_key [-2, 1, 0, -4]
    pkA <- gen_pub_key (skA, csidh_curve)
    putStrLn (show pkA)
    pkB <- gen_pub_key (skB, csidh_curve)
    putStrLn (show pkB)
    (sskA, _, p) <- gen_pub_key (skA, pkB)
    putStrLn (show sskA)
    (sskB, _, p) <- gen_pub_key (skB, pkA)
    putStrLn (show sskB)
    putStrLn (show (point_eq sskA sskB p))
