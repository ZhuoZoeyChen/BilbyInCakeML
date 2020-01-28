theory testFile

imports
   "../lib/FunBucket"
   "../adt/VfsT"
   "../adt/WordArrayT"
   "../lib/CogentMonad"
begin

definition
  afs_rename :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode option \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode \<times> vnode option) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_rename afs vdir oldname oldvnode newname onewvnode \<equiv>
  if a_is_readonly afs then
    return ((afs, vdir, oldvnode, onewvnode), Error eRoFs)
  else do
    old_is_dir \<leftarrow> return ( S_ISDIR (v_mode oldvnode));
    ncnt \<leftarrow> return (if old_is_dir then v_nlink oldvnode - 1 else v_nlink oldvnode);
    oldvnode' \<leftarrow> return (oldvnode \<lparr> v_nlink := ncnt \<rparr>);
    oldinode  \<leftarrow> return ((the $ updated_afs afs (v_ino oldvnode))\<lparr> i_nlink := ncnt \<rparr>);
    (afs, time) \<leftarrow> afs_get_current_time afs;
    newsz \<leftarrow> select UNIV;
    r \<leftarrow> read_afs_inode afs (v_ino vdir);
    case r of
    Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)    
    | Success dir \<Rightarrow> do
    r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa oldname := None, 
                    \<alpha>wa newname := Some (v_ino oldvnode) )) dir) \<sqinter> return (Error eNameTooLong);
    case r of
     Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)
    | Success dir \<Rightarrow> do
    dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time, i_size := newsz\<rparr>);   
    (case onewvnode of
    Some newvnode \<Rightarrow>
     let newinode = the $ updated_afs afs (v_ino newvnode);
         new_is_dir = afs_inode_is_dir (i_type newinode) 
     in return ((afs, vdir, oldvnode, onewvnode), Error eNotEmpty)
      | None \<Rightarrow>
        do
         (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino oldinode \<mapsto> oldinode, i_ino dir \<mapsto> dir));
         case r of
           Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)
         | Success () \<Rightarrow>
           let vdir' = vdir \<lparr> v_mtime := time, v_ctime := time, v_size := newsz \<rparr>
           in return ((afs, vdir', oldvnode', None), Success ())
        od)
     od
  od
od
"

let newinode = the $ updated_afs afs (v_ino newvnode);new_is_dir = afs_inode_is_dir (i_type newinode) in potato 

end