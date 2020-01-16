(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory broken 

imports Main

begin 

text {* High-level Correctness specification types *}

definition
  a_afs_updated_n :: "nat \<Rightarrow> afs_map \<Rightarrow> (afs_map \<Rightarrow> afs_map) list \<Rightarrow> afs_map"
where
 a_afs_updated_n_def[simp]:
 "a_afs_updated_n n afs_st updates = fold id (take n updates) afs_st"

end 
