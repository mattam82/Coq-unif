

Lemma foo : True.
evar (n : nat -> nat). 
pose (m := fix aux m :=
      match m with 
        | 0 => 0
        | S _ => aux (n m)
      end).
pose (eq_refl : n = fun n => n).
assert(eq_refl : m 1 = m 2).
apply eq_refl.
Qed.
