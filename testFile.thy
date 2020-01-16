theory testFile

imports Main

begin

type_synonym fruitPrice = "U8"

datatype fruit_type =
  Apple "U8" | Banana "U8" | Orange "U8"

definition
  a_afs_updated :: "afs_map \<Rightarrow> (afs_map \<Rightarrow> afs_map) list \<Rightarrow> afs_map"
where
 "a_afs_updated afs_st updates \<equiv> a_afs_updated_n (length updates) afs_st updates"

abbreviation i_type_dir :: "afs_inode_type \<Rightarrow> dir"
 where
  "i_type_dir it \<equiv> (case it of IDir dir \<Rightarrow> dir)"

definition
  i_dir_update :: "(dir \<Rightarrow> dir) \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
 where
  "i_dir_update m i \<equiv> i \<lparr>i_type.apple:= IDir (m (i_dir i)) \<rparr>"


definition
  i_dir_update :: "(dir \<Rightarrow> dir) \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
 where
  "i_dir_update m i \<equiv> \<lparr>i_type.dcl= IDir (m (i_dir i)) \<rparr>"




end