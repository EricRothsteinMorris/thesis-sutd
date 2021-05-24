-- shortestSequences::[[[x]]]->([[[x]]],[[[x]]]) --This tries to eat more than they can chew
-- shortestSequences xsss =
--     fmap (foldl consumeHead ([],[])) xsss
--         where
--             --consumeHead::([[x]],[[x]])->[[x]]->([[x]],[[x]])
--             consumeHead acc xss =
--                 fold (\a xs -> if xs ==) xss--[[([x],[x])]] --Probably best to use difference lists.

--We use the state monad combined with coalgebras
import Control.Monad.State
--The state is [[x]] and the output is [[x]]
--Coalgebras help be decide the next state. Just eat one head at a time?
--offWithTheirHeads::([[[x]]],[[[x]]])->([[[x]]],[[[x]]])
-- offWithTheirHeads::([[[x]]],_)->([[[x]]],_) -- a difference list? once you are done
-- offWithTheirHeads ([],_)=([],[])
-- offWithTheirHeads (xsss = fmap passHeads xs


--Let's start basic: this is a coalgebra of the functor 1+(x,[x])

deconstruct::[x]-> ([x]->[x],[x]) --use difference lists
deconstruct []= (id,[])
deconstruct (x:xs) = ((x:),xs)

updateAccLv1::[[x]]->([[x]->[x]],[[x]])
updateAccLv1 xss = fmap deconstruct xss

-- flatten::[Maybe (x,[x])]-> ([x],[[x]])
-- flatten [] =(Nothing,[])
-- flatten xs = 
--     let
--         fmap 


--We could implement our own folding

-- [ [ "a", "bc", "de", "f", "gh" ]
-- , [ "ijk", "lm", "nop", "q"]
-- , [ "rst" ]
-- , [ "uv", "w", "x", "yz"]
-- ]