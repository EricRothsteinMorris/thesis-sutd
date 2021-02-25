
{- imagine there are cannonical functions
unpack:: Functor t => t x -> x
pack:: Functor t => x -> t x

such that they are inverses
(unpack . pack) = id -- in x 
(pack . unpack) = id -- in t x
and 
f <$> (pack x) = pack (f x)  --packing law

then, the function  
<*>:: t(x->y)->t x -> t y
can be implemented by
tf <*> tx = (unpack tf) <$> tx

would this satisfy the applicative laws?

pack id <*> v = v                            -- Identity
pack f <*> pack x = pack (f x)               -- Homomorphism
u <*> pack y = pack ($ y) <*> u              -- Interchange
pack (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition

let's check.

pack id <*> v = (unpack (pack id)) <$> v = id <$> v = id -- Identity is satisfied.
pack f <*> pack x = (unpack (pack f)) <$> pack x = f <$> pack x = pack (f x)

tf <*> pack x =? pack ($ x) <*> tf 
    --first, let's clarify types:
    -- tf:: t (x->y)
    -- pack x:: t x
    -- pack ($ x):: t ((x->y)->y)
    -- ($ x)::(x->y)->y

now, 
pack ($ x) <*> tf = 
    ($ x) <$> tf =
    ($ x) <$> (pack (unpack tf))=
    pack (($ x) (unpack tf)) -- if g= unpack tf, then ($ x) g = g x
    pack ((unpack tf) x) OK

NOW
tf <*> pack x =
    (unpack tf <$> pack x)= 
        pack ((unpack tf) x) -- YAY! we met in the middle!

Interchange is OK

finally, composition. Again, let us first check the types:
tf:: t (x->y)
tg:: t (y->z)
tx:: t x
(tf <*> tx)::t y
tg <*> (tf <*> tx)::t z
(.):: (y->z)->(x->y)->x->z
pack (.) = t ((y->z)->(x->y)->x->z)
--parenthesis are kinda hard here
(pack (.) <*> tg)::t ((x->y)->x->z)
(.) <$> tg::t ((x->y)->x->z)
unpack ((.) <$> tg)::((x->y)->x->z)

pack (.) <*> tg <*> tf <*> tx =
((pack (.) <*> tg) <*> tf) <*> tx =
    ((unpack (pack (.)) <$> tg) <*> tf) <*> tx =
    (((.) <$> tg) <*> tf) <*> tx =
    ((unpack ((.) <$> tg)) <$> tf) <*> tx =


tg <*> (tf <*> tx) =
    (unpack tg) <$> ((unpack tf) <$> tx) = -- ((unpack tg) <$> tx)::ty
    (unpack tg) <$> ((unpack tf) <$> (pack (unpack tx))=
    (unpack tg) <$> (pack ((unpack tf) (unpack tx))) =
    pack ((unpack tg) $ ((unpack tf) (unpack tx))) =
    pack $ ((unpack tg) . (unpack tf)) (unpack tx)=

-}

class (Functor f)=> Structural f where
    unpack::f x -> x -- corresponds to (<-) used in do-notation.
    pack::x->f x     -- corresponds to pure and to return
    --Ah, the smell of adjunctions in the air. No wonder monads arise from this.
    {-  satisfying
    (unpack . pack) = id -- in x 
    (pack . unpack) = id -- in t x
    f <$> (pack x) = pack (f x)
    --this is all you need. The other laws can be proven if these conditions hold.
    -}

-- <!> is our own version of <*>, we will call it "force" because it forces tf into tx
(<!>)::(Structural t)=>t (x->y)-> t x -> t y
(<!>) tf =  ((unpack tf) <$>)


--the obvious instance is the identity wrapper
newtype Id x = Id x deriving (Eq,Show)

instance Functor Id where
    fmap f (Id x) = Id (f x)

instance Structural Id where
    pack = Id
    unpack (Id x) = x

--tf::(Structural t)=> t (x->y)
tf::Id (x->y)
tf=undefined

--tg::(Structural t)=> t (y->z)
tg::Id (y->z)
tg=undefined

--tx::(Structural t)=> t x
tx::Id x
tx=undefined

--every Structural is an Applicative by <!>=<*>
--instance (Functor f) => Applicative f where
instance Applicative Id where
    pure = pack
    (<*>) = (<!>)

--every Structural is a Monad

kCompose::(Structural t)=>(b->t c)->(a->t b)->a->t c
kCompose tg tf = (tg . unpack . tf)

join::(Structural t)=>t (t x) -> t x
join = (unpack <$>) 

bind::(Structural t)=>t a-> (a->t b)->t b
bind ta f = join (f <$> ta)

-- Structurals are always monads, but not all monads are structural.
-- the monad [] is not structural because you cannot unpack from the empty list []
-- HOWEVER, all monads implement a lifted structural thanks to the join.

instance Monad Id where
    return = pack
    >>= = bind

{- Proof that
    
    f (unpack tx) == tx >>= f
    
    Intuitively, this corresponds to what the we expect the binding <- would do,
    but Haskell trucks us when we say x<-[]. What even is x here?

    tx >>= f = 
        join (f <$> tx) = 
        (unpack <$>) (f <$> tx)= --identity
        (unpack <$>) (f <$> (pack (unpack tx)))= --packing law
        (unpack <$>) (pack (f (unpack tx))) = -- packing law
        unpack <$> (pack (f (unpack tx))) = -- packing law
        pack (unpack (f (unpack tx))) = --identity
        f unpack tx

-}

--NOW the big question, is every Structural a monad? 
--To be a monad, you would need a multiplication. Ou
--The only law that is missing is composition

{-pack (.) <!> tg <!> tf <!> tx :: t y =
((pack (.) <!> tg) <!> tf) <!> tx :: t y =
    (((unpack (pack (.))) <$> tg) <!> tf) <!> tx = -- I can use the Structural laws 
    (((.) <$> tg) <!> tf) <!> tx = -- <!> tf
    ((unpack ((.) <$> tg)) <$> tf) <!> tx = -- <!> tx
    (unpack ((unpack ((.) <$> tg)) <$> tf)) <$> tx = -- identity on tf
    (unpack ((unpack ((.) <$> tg)) <$> ((pack.unpack) tf))) <$> tx = --composition 
    (unpack ((unpack ((.) <$> tg)) <$> (pack (unpack tf)))) <$> tx =  -- packing law on (pack (unpack tf))
    (unpack (pack ((unpack ((.) <$> tg)) (unpack tf)))) <$> tx =-- composition of outer unpack and inner pack
    (unpack . pack) ((unpack ((.) <$> tg)) (unpack tf)) <$> tx =-- identity
    ((unpack ((.) <$> tg)) (unpack tf)) <$> tx =-- identity on tg
    ((unpack ((.) <$> ((pack.unpack) tg))) (unpack tf)) <$> tx =-- composition
    ((unpack ((.) <$> (pack (unpack tg)))) (unpack tf)) <$> tx =-- packing law on (pack (unpack tg))
    (  (  unpack ( pack ((.)(unpack tg)) )  ) (unpack tf)   ) <$> tx =-- unpack (pack ((.)(unpack tg)))) is acting on (unpack tf), can decompose again
    (((unpack. pack) ((.)(unpack tg))) (unpack tf)) <$> tx = -- identity
    ((((.)(unpack tg)))(unpack tf)) <$> tx = -- remove unnecessary parenthesis
    (.)(unpack tg)(unpack tf) <$> tx -- DONE! It finally connected

tg <!> (tf <!> tx) =
    (unpack tg) <$> ((unpack tf) <$> tx) = 
    (unpack tg) <$> ((unpack tf) <$> ((pack . unpack) tx)=
    (unpack tg) <$> ((unpack tf) <$> (pack (unpack tx))= -- packing law
    (unpack tg) <$> (pack ((unpack tf) (unpack tx))) = -- packing law again
    pack ((unpack tg) $ ((unpack tf) (unpack tx))) =
    pack $ ((unpack tg) . (unpack tf)) (unpack tx)= -- 
    pack $ ( (.) (unpack tg)(unpack tf)) (unpack tx)= -- use packing law in reverse
    (.) (unpack tg)(unpack tf) <$> pack ((unpack tx)) = -- inverses
    (.) (unpack tg)(unpack tf) <$> tx =  -- (I think this is a reasonable place to land)
-}