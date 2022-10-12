pred image (f : 'a -> 'b) y = exists x, f x = y.
pred injective_in P (f : 'a -> 'b) = 
  forall x y, P x => P y => f x = f y => x = y.
