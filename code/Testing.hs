
flipflop = [True->(True,{True->True,False->False}), False->(False,{True->True,False->False})]

[(fromList [(False,True),(True,False)],

t . flipflop . s (False) = 
    (t . flipflop)(True) =
        t((True,{True->True,False->False}))
        = (False,{True->True,False->False})

t . flipflop . s (True) = 
    (t . flipflop)(False) =
        t((False,{True->True,False->False}))
        = (True,{True->True,False->False})

True->(True,{True->True,False->False})
False -> (False,{True->True,False->False})

fromList [
((False,{True->False,False->False}),(False,{True->False,False->False})),
((False,{True->False,False->True}),(True,{True->False,False->True})),
((False,{True->True,False->False}),(True,{True->True,False->False})),
((False,{True->True,False->True}),(False,{True->False,False->True})),
((True,{True->False,False->False}),(True,{True->False,False->False})),
((True,{True->False,False->True}),(False,{True->True,False->True})),
((True,{True->True,False->False}),(False,{True->True,False->False})),
((True,{True->True,False->True}),(True,{True->True,False->True}))]),



(fromList [(False,True),(True,False)],fromList [((False,{True->False,False->False}),(True,{True->False,False->True})),
((False,{True->False,False->True}),(False,{True->False,False->False})),
((False,{True->True,False->False}),(True,{True->True,False->False})),
((False,{True->True,False->True}),(False,{True->False,False->True})),
((True,{True->False,False->False}),(True,{True->False,False->False})),
((True,{True->False,False->True}),(False,{True->True,False->True})),
((True,{True->True,False->False}),(False,{True->True,False->False})),
((True,{True->True,False->True}),(True,{True->True,False->True}))]),(fromList [(False,True),(True,False)],fromList [((False,{True->False,False->False}),(True,{True->False,False->True})),
((False,{True->False,False->True}),(False,{True->False,False->True})),
((False,{True->True,False->False}),(True,{True->True,False->False})),
((False,{True->True,False->True}),(False,{True->False,False->False})),
((True,{True->False,False->False}),(True,{True->False,False->False})),
((True,{True->False,False->True}),(False,{True->True,False->True})),
((True,{True->True,False->False}),(False,{True->True,False->False})),
((True,{True->True,False->True}),(True,{True->True,False->True}))])]

)),
((
