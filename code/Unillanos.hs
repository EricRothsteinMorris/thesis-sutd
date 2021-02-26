import Data.Char
--Definiciones puras de f, g y h
--f :: Integer -> Integer
--g :: Integer -> Integer
--h :: Integer -> Integer
f=(+2)
g=(*3)
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