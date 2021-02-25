--Our implementation of Heap's algorithm to compute all permutations of elements in X
--This was nice and all but Haskell has Data.List.permutations, which uses less memory
permutations::[x]->[[x]]
permutations xs = generate (length xs) xs
 where
  generate::Int->[x]->[[x]]
  generate k a
    | k==1 = [a] --output (a)
    | otherwise =
      let
        unaltered = generate (k-1) a --Generate permutations with kth unaltered
        --I feel like I need a helper function
        --There is a better way
        altered = concat [generate (k-1) (mutate i (k-1) a) |i<-[0..k-2]] --generateAltered 0 (k-1) a []
      in
        unaltered++altered
          where
            mutate::Int->Int->[x]->[x]
            mutate i k a
              | even k = swapDo i k a
              | otherwise = swapDo 0 k a


          -- generateAltered i k a perms
          --   | i>=k = perms

swapDo::Int->Int->[x]->[x] --How would I know that this function is monadic? because I am building a list?
--to build a list with the constructor we use (x:[]), but this build the list from last to front.
swapDo i j a =
  do
    (k,x) <- zip [0.. length a -1] a -- zip [0.. length a -1] a ::[(Int,x)], but (k,x) are of type (Int,x)
    return $ elemAt (k,x)
      where
        --elemAt::(Int,k)-> x -- is correct, but if I uncomment this the compiler complains
        elemAt (k,x)
          | k==i = a!!j
          | k==j = a!!i
          | otherwise = x

--OK, I think you know you can use a monadic function because you have steps of the form [x]=>[x]=>[x]=>[x].
--you start with an empty list and start adding elements to it.

--Let us translate the function above using bind. They should be equivalent
swapBind::Int->Int->[x]->[x] --
swapBind i j a =
  (zip [0.. length a -1] a) >>= (return . elemAt) --the point here is that we
    where
      --elemAt::(Int, x) -> x
      elemAt (k,x)
        | k==i = a!!j
        | k==j = a!!i
        | otherwise = x

--EXPENSIVE! Because you always have to go back to a to obtain a!!k, but it is super clear at least. This is optimised below
swapListNaive::Int->Int->[x]->[x]
swapListNaive i j a =
  [elemAt k| k <- [0.. length a -1]] --list comprehension
    where
      --elemAt::Int -> x
      elemAt k
        | k==i = a!!j
        | k==j = a!!i
        | otherwise = a!!k

--You can use list comprehension when the monad is the list, but what about other monads? Remember that the List type is recursive though...
swapList::Int->Int->[x]->[x]
swapList i j a =
  [elemAt (k,x)| (k,x) <- zip [0.. length a -1] a] --list comprehension
    where
      --elemAt::(Int, x) -> x
      elemAt (k,x)
        | k==i = a!!j
        | k==j = a!!i
        | otherwise = x

--Ok, this is how I would write it without monads. However, without using zipWith it is very inefficient!!! We have to reverse it because we build backwards
swap::Int->Int->[x]->[x]
swap i j a =
  reverse $ swapHelper (zip [0.. length a -1] a) []
    where
      --swapHelper::Int -> [x] -> [x]
      swapHelper [] res = res
      swapHelper ((k,x):as') res
        | k == i = swapHelper as' ((a!!j):res)
        | k == j = swapHelper as' ((a!!i):res)
        | otherwise = swapHelper as' (x:res)

--It is still, in any case, very inefficient when compared to the monadic implementation.

