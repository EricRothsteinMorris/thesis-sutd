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


type X = Maybe Bool -- Easy enough.
states = [Nothing, Just False, Just True] --the carrier is small, we can enumerate them.
allX = states

data Cont x = Cont {onTrue::x, onFalse::x} deriving (Eq,Ord)

instance (Show x)=> Show (Cont x) where 
  show (Cont t f)="{True:"++(show t)++",False:"++(show f)++"}"

data F x = F {o::Bool,d::Cont x} deriving (Eq,Ord)

data FCoalgX = Behaviour {ofNothing::(F X), ofJustTrue::F X, ofJustFalse::F X} deriving (Eq,Ord,Show)

--allFCoalgx

toFCoalg::(X-> F X) -> FCoalgX
toFCoalg f = Behaviour (f Nothing) (f (Just True)) (f (Just False))

fromFCoalg::FCoalgX->(X->F X)
fromFCoalg (Behaviour n t f) = \x->
  case x of 
    Nothing -> n
    Just True -> t
    Just False -> f

--There are 5832 FCoalgs for this carrier set and this functor. 
allFCoalgs = [Behaviour n t f | n<-allFX, t<-allFX, f<-allFX]

--First we need to identify the trivial transformations
trivialX=M.fromList [(x,x)|x<-states]
trivialFX=M.fromList [(x,x)|x<-allFX]

--Now, this is easier than languages. The question is: given an FCoalg,
solve::FCoalgX->FCoalgX->Maybe (M.Map X X, M.Map (F X) (F X))
solve seed target = 
  solveHelper allTX allTFX
    where 
      allTX = (allTransformations allX)
      allTFX = (allTransformations allFX)
      solveHelper xs fxs = 
        case (xs,fxs) of
          ([],[]) -> Nothing --brute force finished....
          ([],fx:fxs') -> solveHelper allTX fxs'--We ran out of state transformations, but maybe 
          (x:xs',(fx:fx')) -> --test x with fx
            if (manifestX seed x fx)==target then
              Just (x,fx)
            else
              solveHelper xs' (fx:fx')


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
    o = 
      case x of
        Nothing -> True
        otherwise -> False
    d = Cont tx (Just False)
      where 
        tx = case x of 
          Nothing -> Nothing
          Just True -> Nothing
          Just False -> Just True

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


--manifest::(x->F x)->(x->x)->(F x-> F x)->(x->F x)
manifest::(x->F x)->(x->x)->(F x-> F x)->(x->F x)
manifest c m h = h.c.m

manifestX::FCoalgX->(M.Map X X)->(M.Map (F X) (F X))->FCoalgX
manifestX c s t = 
  let
     --Let us use the functions that we have 
     cf = fromFCoalg c
     sf = (s!)
     tf = (t!)
  in
    toFCoalg (tf.cf.sf)

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
    all (\(x,y)-> (m!x, m!y)`elem` bisimxs) bisimxs

-- allPermutations :: [a] -> [M.Map (Bool, Bool) a]
-- allPermutations xs = [M.fromList (zip states a) | a<-(permutations xs)]  --not only permutations, but any function

allTransformations :: Ord a => [a] -> [M.Map a a]
allTransformations xs = [ M.fromList $ zip xs image | image <- (getListsOfSize (length xs) xs)]

allConsistentXTransformations c = filter (isConsistentMap c states ) (allTransformations states)

conXTrans=allConsistentXTransformations end11

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
zeroStar x = 
  case x of 
    Nothing -> F True (Cont (Just False) (Just True)) -- $ asCont (\i-> (i && x1, i && x2))
    Just True -> F False (Cont x x)
    Just False -> F True (Cont (Just False) x)

oneStar::X->F X
oneStar x = 
  case x of 
    Nothing -> F True (Cont (Just False) (Just True)) -- $ asCont (\i-> (i && x1, i && x2))
    Just False -> F False (Cont x x)
    Just True -> F True (Cont (Just False) x)


-- targetZeroStar= (zeroStar,(False,False)) --so,we want the latent coalgebra to have a state:r such that that state is bisimilar to this.
-- targetOneStar= (oneStar,(True,True))
-- targetZeroOneStar= (zeroOneStar,(True,False)) --this is what I want, otherwise it would be OneZeroStar
-- targetOneZeroStar= (zeroOneStar,(False,True)) --this is what I want, otherwise it would be OneZeroStar
-- targetOriginal = (end11,(False,False))
-- targetAny = (allSeqs,(False,False))
-- targetNone = (noSeqs,(False,False))


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