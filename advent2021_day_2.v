Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Decimal.

Open Scope list.

Fixpoint option_list_map{A B:Type}(f:A -> option B)(l:list A) : list B :=
match l with
|nil => nil
|x :: xs => match f x with
            |None => (option_list_map f xs)
            |Some b => b :: (option_list_map f xs)
            end
end.

Open Scope string_scope.

(*if s begins with prefix, returns the rest of the string, otherwise none*)
Fixpoint clear_prefix (s prefix:string) : option string :=
  match s, prefix with
  | _, "" => Some s
  | "", String _ _ => None
  | String hd_s tl_s, String hd_p tl_p =>
           if Ascii.eqb hd_s hd_p
            then clear_prefix tl_s tl_p
            else None
  end.

Fixpoint read_uint (s:string) : option uint :=
match s with
|""           => Some Nil
|String hd tl => 
                (match hd with
                 |"0"%char => option_map D0
                 |"1"%char => option_map D1
                 |"2"%char => option_map D2
                 |"3"%char => option_map D3
                 |"4"%char => option_map D4
                 |"5"%char => option_map D5
                 |"6"%char => option_map D6
                 |"7"%char => option_map D7
                 |"8"%char => option_map D8
                 |"9"%char => option_map D9
                 |_ => fun _:_ => None
                 end) (read_uint tl)
end.

Definition read_nat := fun s:_ => option_map Nat.of_uint (read_uint s).

Fixpoint split_string (s:string)(sep:ascii) : list string :=
match s with
|"" => nil
|String hd tl => if Ascii.eqb hd sep
                  then "" :: (split_string tl sep)
                  else match (split_string tl sep) with
                       |nil => (String hd "") :: nil
                       |cons x xs => (String hd x) :: xs
                       end
end.

Inductive sub_instruction : Set :=
 up : nat -> sub_instruction
|down : nat -> sub_instruction
|forward : nat -> sub_instruction.

Definition read_sub_instruction(s:string) : option sub_instruction.
destruct (clear_prefix s "up ").
destruct (read_nat s0).
apply (Some (up n)).
apply None.

destruct (clear_prefix s "down ").
destruct (read_nat s0).
apply (Some (down n)).
apply None.

destruct (clear_prefix s "forward ").
destruct (read_nat s0).
apply (Some (forward n)).
apply None.

apply None.
Optimize Proof.
Defined.

Require Import Coq.ZArith.ZArith.

Open Scope Z.
Open Scope list.

Fixpoint find_position (course : list sub_instruction) : Z*Z :=
match course with
|nil => (0, 0)
|x :: xs => match (find_position xs) with
            |(n, m) => match x with
                       |up k => (n, m - (BinIntDef.Z.of_nat k))
                       |down k => (n, m + (BinIntDef.Z.of_nat k))
                       |forward k => (n + (BinIntDef.Z.of_nat k), m)
                       end
            end
end.

Require Import Day2_puzzle_input.

Compute (fun p:Z*Z => match p with |(n, m) => n * m end) (find_position (option_list_map read_sub_instruction (split_string Day2_puzzle_input "010"%char))).

Fixpoint find_position_aim_helper (course : list sub_instruction)(hor depth aim:Z) : Z*Z*Z :=
match course with
|nil => (hor, depth, aim)
|x :: xs => let p := match x with
                     |up k => (0, 0, - (BinIntDef.Z.of_nat k))
                     |down k => (0, 0, BinIntDef.Z.of_nat k)
                     |forward k => ((BinIntDef.Z.of_nat k), aim * (BinIntDef.Z.of_nat k), 0)
                     end in
            match p with
            |(hor_delta, depth_delta, aim_delta) => find_position_aim_helper xs (hor + hor_delta) (depth + depth_delta) (aim + aim_delta)
            end
end.

Definition find_position_aim (course : list sub_instruction) : Z*Z*Z := find_position_aim_helper course 0 0 0.

Compute (fun p:Z*Z*Z => match p with |(n, m, _) => n * m end) (find_position_aim (option_list_map read_sub_instruction (split_string Day2_puzzle_input "010"%char))).
