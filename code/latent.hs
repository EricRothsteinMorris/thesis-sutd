--import Control.Monad.State --only works if there are no inputs, otherwise you'll have to curry them :/
import Data.List
import Control.Arrow
import qualified Data.Map as M

-- pairApply::(a->b)->(a->c)->a->(b,c)
-- pairApply = &&&


data F x = F {o::Bool,d::Bool->x }

instance Functor F where
  fmap f (F o d) = (F o (f.d))

data Timed x = Timed{at::Int, value::x} deriving (Eq,Ord)

instance (Show x)=> Show (Timed x) where
  show (Timed t x) = (show x)++" at time "++(show t)

instance Functor Timed where
  fmap f (Timed t x) = Timed t (f x)
  --We cannot map to Timed (f x) (t+1) or we would break the functor rule fmap id = id

instance Applicative Timed where
  pure x = Timed 0 x --careful! lifting puts a zero counter.
  (Timed t f) <*> (Timed t' x) = if t==t' then Timed t (f x) else error ("Desynched lifting of function at time "++(show t')++" in state at time "++(show t))

instance Monad Timed where
  (Timed t x) >>= f =
    let
      (Timed t' y) = f x
    in
      if t==t' then f x else error ("Desynched application of function: expected state at time "++(show t')++", but received state at time "++(show t))
      -- Functions can only be lifted and applied if they are synched. This will be useful when we attack.
      --(Timed t x) >>= (\x->(Timed x 0)) == Timed t x OK only if t==0.
      --(Timed x 0) >>= f = Timed (value $ f x) 0 == f x OK because to apply f to return x its time must be 0

--This is example of a monad that seems like it is useful, but not really.
--We have to make sure to only apply functions that yield state at the right time, or we'll get an error. With fmap we can apply a map x->x to a Timed x, which is probably what we need anyways.
-- to use >>= we would need to use a function x->Timed x, the only functions we know so far of that type is return and Timed t
-- Say we create a function timeAt::Int->x->Timed, where timeAt k x = Timed x k, note that we can only apply (timeAt k) to Timed  k..., so we are writting
-- (Timed x k )>>= (timeAt k) to obtain Timed x k... coooooool.... in other words timeAt k = Timed k

data Three = Zero | One | Two deriving (Show,Eq, Ord)

end11::Three-> F Three
end11 x = F o d
  where
    o = if x==Two then True else False
    d = \i ->
      case (x,i) of
        (_,False) -> Zero
        (Zero,True) -> One
        otherwise -> Two

accepts::(x->F x)->x->[Bool]->Bool -- from coalgebra to behaviour
accepts c x ws = (o . c) (foldl' (d.c) x ws)


step::(x->F x)->Bool->x->x
step c w x = (d.c) x w

type Behaviour = [Bool]->Bool

liftCarrier::(x->F x)->(Timed x-> F (Timed x))
liftCarrier c = \(Timed t x) -> F ( (o.c) x) (\i-> Timed (t+1) ((d.c) x i) )


finalCoalgebra::Behaviour-> F Behaviour
finalCoalgebra rho = F o d
  where
    o   = rho [] --compare this to end11.
    d i = \w-> rho (i:w)

create::F Behaviour -> Behaviour -- reverses the final coalgebra
create (F o d) =
  \ws-> case ws of
    []      -> o
    (w:ws') -> d w ws --consume w and compute with the rest (w::Bool, ws::[Bool], d::Bool->Behaviour)

semantics::(x->F x)-> x-> Behaviour
semantics c x =
  let
    F o d = c x
  in
    \ws->
      case ws of
        []      -> o
        (w:ws') -> semantics c (d w) ws'

type Attack x = M.Map x x--it ismore practical to define it as Map x x for solutions instead of x->x (finite support: if x is not in the map, then we assume a(x)=x).

latentSemantics::(Ord x)=>(x->F x)->(Attack x)->x->Behaviour
latentSemantics c a =
  let
    c' = c.(a!)
  in
    semantics c'

--Note that this operation is always safe.
(!)::(Ord x)=>M.Map x x->x->x
m ! x = case m M.!? x of
  Nothing -> x
  Just x' -> x'

next= M.fromList [(Zero,One),(One,Two),(Two,Zero)]

badBeh= latentSemantics end11 next

-- We should now move to c++ and see how we can solve a problem with Z3. Maybe we can create the problem here and pass it to a class in c++?
--Ok, what is a decision problem?

solveInK::(Timed x->F (Timed x))->Int->Attack (Timed x)->Attack (Timed x)
solveInK c k m =
  if k==0 then
    m
  else
    undefined
    --Try to
    --
