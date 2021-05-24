--import Control.Monad.State --only works if there are no inputs, otherwise you'll have to curry them :/
import Data.List
import qualified Data.Set as S
import Control.Arrow
import qualified Data.Map as M
-- import Control.Functor.Algebra
--import Z3.Monad

-- pairApply::(a->b)->(a->c)->a->(b,c)
-- pairApply = &&&

--We have four states, by pingeonhole principle, any sequence of length 6 or more will be repeating a state.
--x0-i0->x0-i1->x1-i2->x1-i3->x2-i4->x2-i5->x3
allWords = concat $ [getListsOfSize i [False,True]| i<-[0..6]]

allLanguages = [ zip allWords image | image <- (getListsOfSize (length allWords) [False,True])] --[(w,b)| w<-allWords,b<-[False,True]]

{- 
  In a way s:(x->x) deforms space, and t:(F x-> F x) deforms time.
  Ok, 
-}

type X = (Bool, Bool) -- Easy enough.
states = [(a,b)| a<-[False,True], b<-[False,True]] --the carrier is small, we can enumerate them.
allX = states

data Cont x = Cont {onTrue::x, onFalse::x} deriving (Eq,Ord)

flipComponents::X->X
flipComponents (a,b)=(b,a)

shiftR::X->X
shiftR (a,b)=(False,a)

firstIsAlwaysOne::X->X
firstIsAlwaysOne (_,b)=(True,b)

rotateRight::X->X
rotateRight (a,b)=
  case (a,b) of
    (False,False)->(False,True)
    (False,True)->(True,True)
    (True,True)->(True,False)
    (True,False)->(False,False)

notX::X->X
notX (a,b)=(not a,not b)

notFirst::X->X
notFirst (a,b)=(not a,b)

mini::X->X
mini x = 
  if x == (False,True) then
    (False,False)
  else if x == (False,False) then
    (False,True)
  else
    x

test::X->X
test x = 
  case x of 
    (False,_)-> (False,False)
    (True,_)-> (True,True)

instance (Show x)=> Show (Cont x) where 
  show (Cont t f)="{True:"++(show t)++",False:"++(show f)++"}"

data F x = F {o::Bool,d::Cont x} deriving (Eq, Ord)

data FCoalgX = Behaviour {of00::(F X), of01::F X, of10::F X, of11::F X} deriving (Eq,Ord,Show)

instance (Show x)=> Show (F x) where
  show (F o d) = show (o,d)

allFX::[F X] --there are 32
allFX = [F o d | o<-[False,True], d<-allConts]

--There are a lot of deformations of F X; 32^32

asCont::(Bool->x)->Cont x
asCont f = Cont (f True) (f False)

allConts=fmap (\(t,f)->Cont t f) [(a,b)| a<-states, b<-states]

(?)::Cont x->Bool->x
(Cont t f) ? i = if i then t else f

--F is a Functor
instance Functor F where
  fmap h (F o (Cont t f)) = (F o (Cont (h t) (h f)))

--This coalgebra is the baseline
end11::X-> F X
end11 x = F o d
  where
    o = (fst x) && (snd x)
    d = asCont $ \i -> (i, fst x )

accepts::(x->F x)->x->[Bool]->Bool -- from coalgebra to behaviour
accepts c x ws = (o . c) (foldl' ((?).d.c) x ws)

language::(x->F x)->x->[[Bool]]
language c x = filter (accepts c x) allWords 

step::(x->F x)->Bool->x->x
step c = flip ((?).d.c) 

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
                successors = [(((?).d.c1) x i,((?).d.c2) y i)  | i<-[False,True]]
              in
                bisimHelper (successors++todo) (S.insert (x,y) visited) --this is something that could be changed to work with continuations.
                
bisimilarity::(Ord x)=>(x->F x)->[x]->[(x,x)]
bisimilarity c xs = [(x,y)| x<-xs, y<-xs, (bisimilar c c) x y ]

type Transformation x = x->x

--Note that this operation is always safe. It creates a transformation with finite support.
(!)::(Ord x)=>M.Map x x->x->x
m ! x = case m M.!? x of
  Nothing -> x
  Just x' -> x'


manifest::(x->F x)->(x->x)->(F x-> F x)->(x->F x)
manifest c m h = h.c.m

isConsistent::(Eq x, Ord x)=>(x-> F x)->[x]->(x->x)->Bool
isConsistent c xs m = 
  let
    bisimxs = bisimilarity c xs
    newxs = map m xs
  in
    any (\(x,y)->not $ (m x, m y)`elem` bisimxs) bisimxs
  
isConsistentMap::(Eq x, Ord x)=>(x-> F x)->[x]->(M.Map x x)->Bool
isConsistentMap c xs m = 
  let
    bisimxs = bisimilarity c xs
  in
    any (\(x,y)->not $ (m!x, m!y)`elem` bisimxs) bisimxs

allPermutations :: [a] -> [M.Map (Bool, Bool) a]
allPermutations xs = [M.fromList (zip states a) | a<-(permutations xs)]  --not only permutations, but any function

allTransformations :: Ord a => [a] -> [M.Map a a]
allTransformations xs = [ M.fromList $ zip xs image | image <- (getListsOfSize (length xs) xs)]

allConsistentXTransformations c = filter (isConsistentMap c states ) (allTransformations states)

consistentTrans=allConsistentXTransformations end11

allTransformationsOnSnd=filter isValidMap (allTransformations states)--M.filterWithKey (\k v-> (fst k) == (fst v) ) allTransformations 
  where
    isValidMap m =
      all (\(x,x') -> (fst x) == (fst x')) (M.toList m)

allTransformationsOnFst=filter isValidMap (allTransformations states) --M.filterWithKey (\k v-> (fst k) == (fst v) ) allTransformations 
  where
    isValidMap m =
      all (\(x,x') -> (snd x) == (snd x')) (M.toList m)

allTransformationsOnNone=filter isValidMap (allTransformations states) --M.filterWithKey (\k v-> (fst k) == (fst v) ) allTransformations 
  where
    isValidMap m =
      all (\(x,x') -> x==x') (M.toList m)

allLatentCoalgebras = fmap (end11.) (fmap (!) (allTransformations states))  --ok, this has 256 latent coalgebras. What do I do with them?

--We can solve this problem by generating lists of size (length states)
getListsOfSize::Int->[x]->[[x]]
getListsOfSize 0 _ = [[]]
getListsOfSize 1 a = [[x]| x<-a]  
getListsOfSize k a = [(x:s) | x<-a, s<-(getListsOfSize (k-1) a)]  


allSeqs::X->F X
allSeqs x = F True (Cont x x) -- $asCont (const x)

noSeqs::X->F X
noSeqs x = F False (Cont x x)-- $asCont (const x)

zeroStar::X->F X
zeroStar (x1,x2) = F (not (x1 || x2)) (Cont (True,True) (x1,x2))-- $asCont (\i-> (i || x1, i|| x2))

oneStar::X->F X
oneStar (x1,x2) = F (x1 && x2) (Cont (x1,x2) (False,False)) -- $ asCont (\i-> (i && x1, i && x2))

zeroOneStar::X->F X
zeroOneStar x@(x1,x2) = 
  case x of
    (False,False) -> F False $asCont (const sink)
    (False,True)  -> F True $asCont (\i-> if i then (True, False) else sink )
    (True, False) -> F True $asCont(\i-> if (not i) then (False, True) else sink )
    (True, True)  -> F False $asCont(const sink)
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

targetZeroStar= (zeroStar,(False,False)) --so,we want the latent coalgebra to have a state:r such that that state is bisimilar to this.
targetOneStar= (oneStar,(True,True))
targetZeroOneStar= (zeroOneStar,(True,False)) --this is what I want, otherwise it would be OneZeroStar
targetOneZeroStar= (zeroOneStar,(False,True)) --this is what I want, otherwise it would be OneZeroStar
targetOriginal = (end11,(False,False))
targetAny = (allSeqs,(False,False))
targetNone = (noSeqs,(False,False))


bruteforceCarrier::(Ord x, Ord y)=> (x->F x)-> [Transformation x]-> [x]->((y->F y),y) -> Maybe (x,Transformation x)
bruteforceCarrier c transformations states behaviour@(targetCoalgebra,targetState) = 
  case transformations of
    [] -> Nothing
    (a:transformations') -> 
      let
        c' = (c.a) --get the latent coalgebra
      in
        case findTargetState c' of
          Just x -> Just (x,a)
          Nothing -> --try the next Transformation
            bruteforceCarrier c transformations' states behaviour
        where
          findTargetState c' = find (\x-> bisimilar c' targetCoalgebra x targetState) states          

bruteforceInitial::(Ord x, Ord y)=> (x->F x)-> [Transformation x]-> [x]->x->((y->F y),y) -> Maybe (x,Transformation x)
bruteforceInitial c transformations states x0 behaviour@(targetCoalgebra,targetState) = 
  case transformations of
    [] -> Nothing
    (a:transformations') -> 
      let
        c' = (c.a) --get the latent coalgebra
      in
        if bisimilar c' targetCoalgebra x0 targetState then
          Just (x0,a)
        else
            bruteforceInitial c transformations' states x0 behaviour

bruteforceDynamics::(Ord x, Ord y)=> (x->F x)-> [Transformation (F x) ]-> [x]->((y->F y),y) -> Maybe (x,Transformation (F x))
bruteforceDynamics c transformations states behaviour@(targetCoalgebra,targetState) = 
  case transformations of
    [] -> Nothing
    (h:transformations') -> 
      let
        c' = (h.c) --get the latent coalgebra
      in
        case findTargetState c' of
          Just x -> Just (x,h)
          Nothing -> --try the next Transformation
            bruteforceDynamics c transformations' states behaviour
        where
          findTargetState c' = find (\x-> bisimilar c' targetCoalgebra x targetState) states

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
            x' = ((?).d.c) x $ i
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


--Here are some transformations of F X

complement::Transformation (F X)
complement (F o d) = (F (not o) d)

powerset::[b]->[[b]]
powerset bs = subsets bs (length bs)

subsets:: [b] -> Int -> [[b]]
subsets _ 0 = [[]]
subsets [] _ = [[]]
subsets (x:xs) k =
  let
    withoutX= subsets xs k
    forcingX= map (x:)(subsets xs (k-1))
  in
    withoutX++forcingX


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

--To solve a problem: find an Transformation a such that the (latent end11 a)

-- We should now move to c++ and see how we can solve a problem with Z3. Maybe we can create the problem here and pass it to a class in c++?
--Ok, what is a decision problem?
--
-- solveInK::(Timed x->F (Timed x))->Int->Transformation (Timed x)->Transformation (Timed x)
-- solveInK c k m =
--   if k==0 then
--     m
--   else
--     undefined
--     --Try to
--     --