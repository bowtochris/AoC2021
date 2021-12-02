Open Scope list_scope.

Fixpoint SonarSweepHelper(x:nat)(xs:list nat) : nat :=
match xs with
|nil => O
|y :: ys => match Nat.ltb x y with
            |true  => S (SonarSweepHelper y ys)
            |false => SonarSweepHelper y ys
            end
end.

Definition SonarSweep(xs:list nat) : nat :=
match xs with
|nil => O
|y :: ys => SonarSweepHelper y ys
end.

Require Import Day1_puzzle_input.

(*Answer to day one part 1*)
Compute (SonarSweep Day1_puzzle_input).

Fixpoint sliding_triples {A:Type}(l: list A) : list (A*A*A) :=
  match l with
  | nil | _ :: nil | _ :: _ :: nil => nil
  | x :: (y :: z :: _) as xs => (x, y, z) :: sliding_triples xs
  end.

Require Import Coq.Lists.List.

Definition SonarSweep_sliding_triples(xs:list nat) : nat := SonarSweep (map (fun p:nat*nat*nat => match p with |(a, b, c) => a + b + c end) (sliding_triples xs)).

(*Answer to day one part 2 *)
Compute (SonarSweep_sliding_triples Day1_puzzle_input).
