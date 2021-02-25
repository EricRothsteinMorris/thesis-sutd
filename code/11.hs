--import Control.Monad.State --only works if there are no inputs, otherwise you'll have to curry them :/
import Data.List
import qualified Data.Set as S
import Control.Arrow
import qualified Data.Map as M

-- pairApply::(a->b)->(a->c)->a->(b,c)
-- pairApply = &&&

type X = (Bool, Bool) -- Easy enough.
states = [(a,b)| a<-[False,True], b<-[False,True]] --the carrier is small, we can enumerate them.

data F x = F {o::Bool,d::Bool->x }

instance Functor F where
  fmap f (F o d) = (F o (f.d))



end11::X-> F X
end11 x = F o d
  where
    o = (fst x) && (snd x)
    d = \i -> (i, fst x )

accepts::(x->F x)->x->[Bool]->Bool -- from coalgebra to behaviour
accepts c x ws = (o . c) (foldl' (d.c) x ws)

step::(x->F x)->Bool->x->x
step c w x = (d.c) x w

type Behaviour = [Bool]->Bool

bisimilar::(Ord x,Ord y)=>(x->F x)->(y->F y)->x->y->Bool
bisimilar c1 c2 x y =
  bisimHelper [(x,y)] S.empty 
    where
      bisimHelper todo visited =
        case todo of 
          [] -> True
          ((x,y):todo') -> 
            if S.member (x,y) visited then bisimHelper todo' visited
            else if (o.c1) x /= (o.c2) y then False
            else 
              let
                successors = [((d.c1) x i,(d.c2) y i)  | i<-[False,True]]
              in
                bisimHelper (successors++todo) (S.insert (x,y) visited) --this is something that could be changed to work with continuations.
                
bisimilarity::(Ord x)=>(x->F x)->[x]->[(x,x)]
bisimilarity c xs = [(x,y)| x<-xs, y<-xs, (bisimilar c c) x y ]

finalCoalgebra::Behaviour-> F Behaviour
finalCoalgebra rho = F o d
  where
    o   = rho []
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

allPermutationAttacks = [M.fromList a | a<-(permutations states)]  --not only permutations, but any function

allAttacks = [ M.fromList $ zip states image | image <- (getListsOfSize (length states) states)]

allLatentCoalgebras = fmap (\a-> latent a end11) allAttacks  --ok, this has 256 latent coalgebras. What do I do with them?

--We can solve this problem by generating lists of size (length states)
getListsOfSize::Int->[x]->[[x]]
getListsOfSize 0 _ = []
getListsOfSize 1 a = [[x]| x<-a]  
getListsOfSize k a = [(x:s) | x<-a, s<-(getListsOfSize (k-1) a)]  


latent::(Ord x)=>(Attack x)->(x->F x)->x->F x
latent a c = c.(a!)

latentSemantics::(Ord x)=>(Attack x)-> (x->F x)->x->Behaviour
latentSemantics a = (semantics . (latent a))

--Note that this operation is always safe.
(!)::(Ord x)=>M.Map x x->x->x
m ! x = case m M.!? x of
  Nothing -> x
  Just x' -> x'

zeroStar::X->F X
zeroStar (x1,x2) = F (not (x1 || x2)) (\i-> (i || x1, i|| x2))

oneStar::X->F X
oneStar (x1,x2) = F (x1 && x2) (\i-> (i && x1, i && x2))

zeroOneStar::X->F X
zeroOneStar x@(x1,x2) = 
  case x of
    (False,False) -> F False (const sink)
    (False,True)  -> F True (\i-> if i then (True, False) else sink )
    (True, False) -> F True (\i-> if (not i) then (False, True) else sink )
    (True, True)  -> F False (const sink)
  where
    sink = (False,False)


targetBehaviour::Behaviour 
targetBehaviour = not . (elem True) -- == semantics all0 (False,False)

targetZeroStar= (zeroStar,(False,False)) --so,we want the latent coalgebra to have a state:r such that that state is bisimilar to this.
targetOneStar= (oneStar,(True,True))
targetZeroOneStar= (zeroOneStar,(True,False)) --this is what I want, otherwise it would be OneZeroStar

bruteforce::(Ord x, Ord y)=> (x->F x)-> [Attack x]-> [x]->((y->F y),y) -> Maybe (x,Attack x)
bruteforce c attacks states behaviour@(targetCoalgebra,targetState) = 
  case attacks of
    [] -> Nothing
    (a:attacks') -> 
      let
        c' = latent a c --get the latent coalgebra
      in
        case findTargetState c' of
          Just x -> Just (x,a)
          Nothing -> --try the next attack
            bruteforce c attacks' states behaviour
        where
          findTargetState c' = find (\x-> bisimilar c' targetCoalgebra x targetState) states
          

--bisimilar cannot be used with behaviours because they are not Ord and not Eq

--To solve a problem: find an attack a such that the (latent end11 a)

-- We should now move to c++ and see how we can solve a problem with Z3. Maybe we can create the problem here and pass it to a class in c++?
--Ok, what is a decision problem?
--
-- solveInK::(Timed x->F (Timed x))->Int->Attack (Timed x)->Attack (Timed x)
-- solveInK c k m =
--   if k==0 then
--     m
--   else
--     undefined
--     --Try to
--     --
