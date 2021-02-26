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

type Attack x = M.Map x x--it is more practical to define it as Map x x for solutions instead of x->x (finite support: if x is not in the map, then we assume a(x)=x).

allPermutationAttacks = [M.fromList (zip states a) | a<-(permutations states)]  --not only permutations, but any function
allAttacks = [ M.fromList $ zip states image | image <- (getListsOfSize (length states) states)]
allAttacksOnSnd=filter isValidMap allAttacks --M.filterWithKey (\k v-> (fst k) == (fst v) ) allAttacks 
  where
    isValidMap m =
      all (\(x,x') -> (fst x) == (fst x')) (M.toList m)
allAttacksOnFst=filter isValidMap allAttacks --M.filterWithKey (\k v-> (fst k) == (fst v) ) allAttacks 
  where
    isValidMap m =
      all (\(x,x') -> (snd x) == (snd x')) (M.toList m)

allAttacksOnNone=filter isValidMap allAttacks --M.filterWithKey (\k v-> (fst k) == (fst v) ) allAttacks 
  where
    isValidMap m =
      all (\(x,x') -> x==x') (M.toList m)

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

allSeqs::X->F X
allSeqs x = F True (const x)

noSeqs::X->F X
noSeqs x = F False (const x)

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

shortString::Bool->String
shortString b
  | b = "1"
  | otherwise = "0"
  
getString::X->String
getString (x,y)= "("++(shortString x)++","++(shortString y)++")"

getStateId::X->String
getStateId (x,y)=(shortString x)++(shortString y)

getWrappedStateId::X->String
getWrappedStateId x="("++(getStateId x)++")"

targetBehaviour::Behaviour 
targetBehaviour = not . (elem True) -- == semantics all0 (False,False)

targetZeroStar= (zeroStar,(False,False)) --so,we want the latent coalgebra to have a state:r such that that state is bisimilar to this.
targetOneStar= (oneStar,(True,True))
targetZeroOneStar= (zeroOneStar,(True,False)) --this is what I want, otherwise it would be OneZeroStar
targetOneZeroStar= (zeroOneStar,(False,True)) --this is what I want, otherwise it would be OneZeroStar
targetOriginal = (end11,(False,False))
targetAny = (allSeqs,(False,False))
targetNone = (noSeqs,(False,False))

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
          

bruteforceInitial::(Ord x, Ord y)=> (x->F x)-> [Attack x]-> [x]->x->((y->F y),y) -> Maybe (x,Attack x)
bruteforceInitial c attacks states x0 behaviour@(targetCoalgebra,targetState) = 
  case attacks of
    [] -> Nothing
    (a:attacks') -> 
      let
        c' = latent a c --get the latent coalgebra
      in
        if bisimilar c' targetCoalgebra x0 targetState then
          Just (x0,a)
        else
            bruteforceInitial c attacks' states x0 behaviour

toTikz c =
  "\\begin{tikzpicture}\n" ++ 
  stateDefs ++
  "\\draw "++
  arrowDefs ++
  ";"++
  "\\end{tikzpicture}"
  where
    ff= getStateId (False,False)
    tf= getStateId (True,False)
    ft= getStateId (False,True)
    tt= getStateId (True,True)
    wff= "("++ff++")"
    wtf= "("++tf++")"
    wft= "("++ft++")"
    wtt= "("++tt++")"
    showAccepting x
      | (o.c) x = ", accepting"
      | otherwise = ""
    arrowDefs = concat$  fmap defArrow [(s,i)|s<-states,i<-[True,False]]
      where
        defArrow (x,i) = 
          let
            x' = (d.c) x $ i
          in
            if x==x' then
              --loop above
              (getWrappedStateId x)++" edge[loop above] node{"++(shortString i)++"} "++(getWrappedStateId x)++"\n"
            else
              --bend right
              (getWrappedStateId x)++" edge[bend left, above] node{"++(shortString i)++"} "++(getWrappedStateId x')++"\n"

    stateDefs = concat$  fmap defState states
      where
        defState x = 
          case x of 
            (False,False)-> "\\node[state"++(showAccepting x)++"] "++wff++" {$"++ (getString x)++"$};\n"
            (True,False)->"\\node[state"++(showAccepting x)++", above right  of="++ff++"] "++wtf++" {$"++ (getString x)++"$};\n"
            (False,True)->"\\node[state"++(showAccepting x)++", below right of="++ff++"] "++wft++" {$"++ (getString x)++"$};\n"
            (True,True)->"\\node[state"++(showAccepting x)++", below right of="++tf++"] "++wtt++" {$"++ (getString x)++"$};\n"
                
-- \node[state] (q1) {$0$};
-- \node[state, right of=q1] (q2) {$1$};
-- \node[state, right of=q2] (q3) {$2$};
-- \draw (q1) edge[loop above] node{0} (q1)
-- (q1) edge[bend left, above] node{1} (q2)
-- (q2) edge[bend left, above] node{0} (q1)
-- (q2) edge[loop above] node{1} (q2)
-- (q3) edge[bend left, above] node{1} (q2)
-- (q3) edge[bend left, below] node{0} (q1);
-- \end{tikzpicture}

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