import Data.Char
import qualified Data.Set as S
--Definiciones puras de f, g y h
--f :: Integer -> Integer
--g :: Integer -> Integer
--h :: Integer -> Integer
f=(+2)
g=(*10)
h=(+(-1))

--
    -- f = map toLower
    -- g = splitAt 2
    -- h = fmap $ filter (isLetter)

--Definición de composición clásica (;)
(>>>)::(x->y)->(y->z)->x->z
(>>>)= flip (.)

--Programa original
program = f >>> g >>> h -- (>>> es ;)

--Función para cambiar el tipo de funciones
reg::(Show x)=>(x->y)->x->(String,y)
reg f x = (show x, f x)

--Nueva composición
($$$)::(x->(String,y))->(y->(String,z))->x->(String,z)
(f $$$ g) x = 
    let
        (lx,y)= f x
        (ly,z)= g y
    in
        (lx++","++ly,z)

--Nuevo programa
program' = (reg f) $$$ (reg g) $$$ (reg h)

linearCommon [] _ = []
linearCommon _ [] = []
linearCommon xs@(x:xs') ys@(y:ys')
    | x==y = x:(linearCommon xs' ys')
    | x<y  = linearCommon xs' ys
    | x>y  = linearCommon xs  ys'

usingSet::(Ord x)=>[x]->[x]->S.Set x
usingSet xs ys =
    S.intersection (S.fromList xs) (S.fromList ys)

usingFoldr xs ys = foldr (\y acc -> if elem y xs then y:acc else acc) [] ys
-- data Zippable x = Zippable [x] [x]

-- instance Foldable (Zippable) where
--     foldMap f (Zippable xs ys) =
--         case (xs,ys) of
--             ([],_) -> mempty
--             (_,[]) -> mempty
--             (x:xs',y:ys') -> --f 