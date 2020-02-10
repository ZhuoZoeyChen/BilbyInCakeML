(* Isabelle


lemmas my_group = TRUTH FALSITY

 *)

open bossLib;
open zoeyLib;

Theorem kjblk:
  T
Proof
 cheat
QED


fun mk_list_conj [] = raise Domain
  | mk_list_conj [e] = e
  | mk_list_conj (f::l) =
    CONJ f (mk_list_conj(l))

Theorem my_group = mk_list_conj [TRUTH,FALSITY,TRUTH]

Theorem my_group = foldr ((uncurry o C)CONJ) (hd [TRUTH,FALSITY,TRUTH]) (tl [TRUTH,FALSITY,TRUTH])

Theorem my_group = foldl ((uncurry)CONJ) (hd [TRUTH,FALSITY,TRUTH]) (tl [TRUTH,FALSITY,TRUTH])

Theorem my_group = foldr ((uncurry)CONJ) (last [TRUTH,FALSITY,TRUTH]) (butlast [TRUTH,FALSITY,TRUTH])


Theorem my_group = CONJ TRUTH (CONJ FALSITY TRUTH)


(*  Isabelle

definition my_const :: "'a => bool"
where "my_const = ARB"

 *)


Definition my_const_def:
    (my_const:'a -> bool) = ARB
End


(* Isabelle


theorem foo:
  "A ==> A"

theorem foo:
  assumes "A"
  shows "A"

theorem foo:
  fixes A :: "bool"
  assumes "A"
  shows "A"

 *)


(* Isabelle



theorem foo:
  fixes x::"'a::group"
  shows "x + (x + x) = (x + x) + x"
  ...
 *)

Theorem foo:
  !+ 0.
  is_group + 0 ==>
  x + (x + x) = (x + x) + x


(*
  instantiation "nat::group"
    <proof>


  [simp]
  [elim]
  [dest]
 *)

Theorem nat_group_instantiation:
  is_group + (0:nat)
Proof
  <proof>
QED
                            
Theorem foo:
  A:bool ==> A
Proof
 ...
QED


Theorem foo:
  
Proof
 ...
QED



Definition kjnkl:
 ll x = 1 + ll x
End

val kjnkl = tDefine "kjnkl"
  `ll x = 1 + ll x`
  (cheat)

Theorem wlnlkn: F
Proof
 assume_tac kjnkl >> fs[]
QED

Theorem nnn: 1 = 2
Proof
  assume_tac wlnlkn >> fs[]
  
  goal_assum kall_tac >> rw[]
  
  simp[] >> metis_tac[wlnlkn]
  match_mp_tac FALSITY >> ACCEPT_TAC wlnlkn
QED



 ll x = 1 + ll x

 0 = 1

val _ = Theory.new_constant("my_face",``:'a``);

val my_face_ax1 = Theory.new_axiom("my_face_ax1",``my_face = T``);

val my_face_ax2 = Theory.new_axiom("my_face_ax2",``my_face = 1``);

  if null [TRUTH,FALSITY] then
    
  else
kljbb
    




foldr (uncurry CONJ) TRUTH [TRUTH,FALSITY]

CONJ TRUTH FALSITY

list_mk_comb(``$/\``,[TRUTH,FALSITY])

TRUTH
FALSITY