open FunBucketTheory;
open VfsTTheory;
open WordArrayTTheory;
open CogentMonadTheory;
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax();
val _ = new_theory"AfsSD"

Type  byte = " U8";


Type  page = " U8 list";


Type  dir = " U8 list ->  Ino option";


Type  file_data = " page list";


Datatype:
 afs_inode_type =
  IDir  dir|
  IReg  file_data|
  ILnk  U8 list
End


Definition 
  afs_inode_is_dir x = ?v. IDir v = x
End

Definition 
  afs_inode_is_reg x = ?v. IReg v = x
End

Definition 
  afs_inode_is_lnk x = ?v. ILnk v = x
End

Datatype:
afs_inode = <|
  i_type :  afs_inode_type;
  i_ino :  Ino;
  i_nlink :  U32;
  i_size :  U64;
  i_mtime :  TimeT;
  i_ctime :  TimeT;
  i_uid :  U32;
  i_gid :  U32;
  i_mode :  Mode;
  i_flags :  U32
|>
End


Type  readdir_ctx = " U32 #  dir";


Type  afs_map = " Ino ->  afs_inode option";


Datatype:
afs_state = <|
  a_is_readonly : bool;
  a_current_time :  TimeT;
  a_medium_afs :  afs_map;
  a_medium_updates : ( afs_map ->  afs_map) list
|>
End


Definition a_afs_updated_n_def:
  a_afs_updated_n n afs_st updates = fold id (take n updates) afs_st
End

export_rewrites "a_afs_updated_n_def"


Definition a_afs_updated_def:
  a_afs_updated afs_st updates = a_afs_updated_n (length updates) afs_st updates
End

Definition updated_afs_def:
  updated_afs adata = a_afs_updated (a_medium_afs adata) (a_medium_updates adata)
End

Overload i_type_dir =   ``i_type_dir it = (case it of
                        | IDir dir => dir)``

Overload i_dir =   ``i_dir i = i_type_dir (i_type i)``

Definition i_dir_update_def:
  i_dir_update m i = i <| i_type := IDir (m (i_dir i)) |>
End

export_rewrites "i_dir_update_def"


Overload i_type_data =   ``i_type_data it = (case it of
                         | IReg data => data)``

Overload i_data =   ``i_data i = i_type_data (i_type i)``

Overload i_data_update =   ``i_data_update m i = i <| i_type := IReg (m (i_data i)) |>``

Overload i_type_path =   ``i_type_path it = (case it of
                         | ILnk path => path)``

Overload i_path =   ``i_path i = i_type_path (i_type i)``

Overload i_path_update =   ``i_path_update m i = i <| i_type := ILnk (m (i_path i)) |>``

Definition i_size_from_afs_inode_type_def:
(i_size_from_afs_inode_type (IDir dir) = undefined)/\
(i_size_from_afs_inode_type (IReg data) = count (concat data))/\
(i_size_from_afs_inode_type (ILnk path) = count path)
End


Overload i_size_from_type =   ``i_size_from_type i = i_size_from_afs_inode_type $ i_type i``

Definition afs_inode_to_vnode_def:
  afs_inode_to_vnode i = <| v_ino := i_ino i;
  v_nlink := i_nlink i;
  v_size := i_size i;
  v_mtime := i_mtime i;
  v_ctime := i_ctime i;
  v_uid := i_uid i;
  v_gid := i_gid i;
  v_mode := i_mode i;
  v_flags := i_flags i |>
End

Definition afs_inode_from_vnode_def:
  afs_inode_from_vnode v = <| i_type := (if v_mode v AND s_IFREG <> 0 then IReg [] else (if v_mode v AND s_IFDIR <> 0 then IDir Map.empty else ILnk []));
  i_ino := v_ino v;
  i_nlink := v_nlink v;
  i_size := v_size v;
  i_mtime := v_mtime v;
  i_ctime := v_ctime v;
  i_uid := v_uid v;
  i_gid := v_gid v;
  i_mode := v_mode v;
  i_flags := v_flags v |>
End

Definition error_if_readonly_def:
  error_if_readonly as = return $ (if a_is_readonly as then Error (eRoFs, as) else Success as)
End

Definition nondet_error_def:
  nondet_error errs f = CogentMonad.select errs >>= (return o f)
End

Definition afs_alloc_inum_def:
  afs_alloc_inum as = do
  avail_inums <- return $ -dom as;
  opt_inum <- select $ {option.None} UNION option.Some ` avail_inums;
  return $ (if opt_inum = option.None then Error () else Success (the opt_inum))
  od
End

Definition afs_get_current_time_def:
  afs_get_current_time afs = do
  time' <- return (a_current_time afs);
  time <- select {x. x >= time'};
  return (afs <| a_current_time := time |>, time')
  od
End

Definition afs_init_inode_def:
  afs_init_inode adata vdir vnode mode = do
  (adata, time) <- afs_get_current_time adata;
  uid <- return (v_uid vdir);
  gid <- return (v_gid vdir);
  vnode <- return (vnode <| v_ctime := time;
  v_mtime := time;
  v_uid := uid;
  v_gid := gid;
  v_mode := mode;
  v_nlink := 1;
  v_size := 0 |>);
  r <- afs_alloc_inum (updated_afs adata);
  return (case r of
  | Error () => Error (adata, vnode)
  | Success inum => Success (adata, vnode <| v_ino := inum |>))
  od
End

Definition read_afs_inode_def:
  read_afs_inode adata ino = return (Success $ the $ updated_afs adata ino) TODO: Alt nondet_error {eIO;
  eNoMem;
  eInval;
  eBadF} Error
End

Definition afs_apply_updates_nondet_def:
  afs_apply_updates_nondet afs = do
  (to_apply, updates) <- {(ap, up). ap @ up = a_medium_updates afs};
  return (afs <| a_medium_afs := fold id to_apply (a_medium_afs afs);
  a_medium_updates := updates |>)
  od
End

Definition afs_update_def:
  afs_update afs upd = do
  afs <- afs_apply_updates_nondet (afs <| a_medium_updates := a_medium_updates afs @ [upd] |>);
  (if a_medium_updates afs = [] then return (afs, Success ()) else return (afs, Success ()) TODO: Alt nondet_error {eIO;
  eNoSpc;
  eNoMem} (\e. (afs <| a_medium_updates := butlast (a_medium_updates afs) |>, Error e)))
  od
End

Definition afs_create_def:
  afs_create afs parentdir name mode vnode = (if a_is_readonly afs then return ((afs, parentdir, vnode), Error eRoFs) else do
  r <- afs_init_inode afs parentdir vnode (mode OR s_IFREG);
  (case r of
  | Error (afs, vnode) => return ((afs, parentdir, vnode), Error eNFile)
  | Success (afs, vnode) => do
  r <- read_afs_inode afs (v_ino parentdir);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAALPHAwa name) -> v_ino vnode)) dir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- select (Success ` {sz. sz > v_size parentdir}) TODO: Alt return (Error eOverflow);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success newsz => do
  time <- return (v_ctime vnode);
  dir <- return (dir <| i_ctime := time;
  i_mtime := time |>);
  inode <- return (afs_inode_from_vnode vnode);
  (afs, r) <- afs_update afs (\f. f ((i_ino inode) -> inode, (i_ino dir) -> dir));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => return ((afs, parentdir <| v_ctime := time;
  v_mtime := time;
  v_size := newsz |>, vnode), Success ()))
  od)
  od)
  od)
  od)
  od)
End

Definition afs_sync_def:
  afs_sync afs = (if a_is_readonly afs then return (afs, Error eRoFs) else do
  n <- select {0..length (a_medium_updates afs)};
  let updates = a_medium_updates afs;
  (to_apply, updates) = (take n updates, drop n updates);
  afs = a_medium_afs_update (fold (\upd med. upd med) to_apply) afs;
  afs = a_medium_updates_update (\_. updates) afs
  in
  (if updates = [] then return (afs, Success ()) else do
  e <- select {eIO;
  eNoMem;
  eNoSpc;
  eOverflow};
  return (afs <| a_is_readonly := e = eIO |>, Error e)
  od)
  od)
End

Definition afs_unlink_def:
  afs_unlink afs parentdir name vnode = do
  r <- error_if_readonly afs;
  (case r of
  | Error (e, afs) => return ((afs, parentdir, vnode), Error e)
  | Success afs => do
  (afs, time) <- afs_get_current_time afs;
  inode <- return ((the $ updated_afs afs (v_ino vnode)) <| i_nlink := v_nlink vnode - 1;
  i_ctime := time |>);
  newsize <- select {sz. sz < v_size parentdir};
  dir_ino <- return (v_ino parentdir);
  (afs, r) <- afs_update afs (\f. f (dir_ino -> i_dir_update (\d. d ((ALPHAwa name) |-> option.None)) (the $ f dir_ino) <| i_ctime := time;
  i_mtime := time |>, (v_ino vnode) -> inode));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => let vnode' = vnode <| v_nlink := v_nlink vnode - 1;
  v_ctime := time |>;
  parentdir' = parentdir <| v_ctime := time;
  v_mtime := time;
  v_size := newsize |>
  in
  return ((afs, parentdir', vnode'), Success ()))
  od)
  od
End

Definition afs_iget_def:
  afs_iget afs inum vnode = (if inum IN dom (updated_afs afs) then do
  r <- read_afs_inode afs inum;
  (case r of
  | Success inode => return (afs_inode_to_vnode inode, Success ())
  | Error e => return (vnode, Error e))
  od else return (vnode, Error eNoEnt))
End

Definition afs_lookup_def:
  afs_lookup afs vdir name = (if wordarray_length name > bilbyFsMaxNameLen + 1 then return (Error eNameTooLong) else do
  r <- read_afs_inode afs (v_ino vdir);
  (case r of
  | Error e => return (Error e)
  | Success dir => (case i_dir dir (ALPHAwa name) of
  | None => return (Error eNoEnt)
  | Some ino => return (Success ino)))
  od)
End

Definition afs_link_def:
  afs_link afs parentdir name vnode = (if a_is_readonly afs then return ((afs, parentdir, vnode), Error eRoFs) else do
  r <- read_afs_inode afs (v_ino parentdir);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa name) -> v_ino vnode)) dir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- select (Success ` {sz. sz > v_size parentdir}) TODO: Alt return (Error eOverflow);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success newsz => do
  time <- return (v_ctime vnode);
  dir <- return (dir <| i_ctime := time;
  i_mtime := time;
  i_size := newsz |>);
  inode <- return (the $ updated_afs afs (v_ino vnode));
  (afs, r) <- afs_update afs (\f. f ((i_ino inode) -> inode, (i_ino dir) -> dir));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => return ((afs, parentdir <| v_ctime := time;
  v_mtime := time;
  v_size := newsz |>, vnode <| v_nlink := v_nlink vnode + 1 |>), Success ()))
  od)
  od)
  od)
  od)
End

Definition afs_mkdir_def:
  afs_mkdir afs parentdir name mode vnode = (if a_is_readonly afs then return ((afs, parentdir, vnode), Error eRoFs) else do
  r <- afs_init_inode afs parentdir vnode (mode OR s_IFDIR);
  (case r of
  | Error (afs, vnode) => return ((afs, parentdir, vnode), Error eNFile)
  | Success (afs, vnode) => do
  r <- read_afs_inode afs (v_ino parentdir);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa name) -> v_ino vnode)) dir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- select (Success ` {sz. sz > v_size parentdir}) TODO: Alt return (Error eOverflow);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success newsz => do
  time <- return (v_ctime vnode);
  dir <- return (dir <| i_ctime := time;
  i_mtime := time;
  i_nlink := i_nlink dir + 1;
  i_size := newsz |>);
  vnode <- return (vnode <| v_nlink := 2 |>);
  inode <- return (afs_inode_from_vnode vnode);
  (afs, r) <- afs_update afs (\f. f ((i_ino inode) -> inode, (i_ino dir) -> dir));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => return ((afs, parentdir <| v_nlink := v_nlink parentdir + 1;
  v_ctime := time;
  v_mtime := time;
  v_size := newsz |>, vnode), Success ()))
  od)
  od)
  od)
  od)
  od)
End

Definition afs_rmdir_def:
  afs_rmdir afs parentdir name vnode = do
  r <- error_if_readonly afs;
  (case r of
  | Error (e, afs) => return ((afs, parentdir, vnode), Error e)
  | Success afs => (if dom (i_dir (the $ updated_afs afs (v_ino vnode))) <> {} then return ((afs, parentdir, vnode), Error eNotEmpty) else do
  (afs, time) <- afs_get_current_time afs;
  vnode' <- return (vnode <| v_nlink := 0 |>);
  inode <- return (afs_inode_from_vnode vnode);
  newsize <- select {sz. sz < v_size parentdir};
  dir_ino <- return (v_ino parentdir);
  parentdir' <- return (parentdir <| v_nlink := v_nlink parentdir - 1;
  v_ctime := time;
  v_mtime := time;
  v_size := newsize |>);
  (afs, r) <- afs_update afs (\f. f (dir_ino -> i_dir_update (\d. d ((ALPHAwa name) |-> option.None)) (the $ f dir_ino) <| i_ctime := time;
  i_mtime := time;
  i_nlink := v_nlink parentdir' |>, (v_ino vnode) -> inode));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => return ((afs, parentdir', vnode'), Success ()))
  od))
  od
End

Definition afs_symlink_def:
  afs_symlink afs parentdir name symname mode vnode = (if a_is_readonly afs then return ((afs, parentdir, vnode), Error eRoFs) else (if wordarray_length symname > bilbyFsBlockSize then return ((afs, parentdir, vnode), Error eNameTooLong) else do
  r <- afs_init_inode afs parentdir vnode (mode OR s_IFLNK OR s_IRWXUGO);
  (case r of
  | Error (afs, vnode) => return ((afs, parentdir, vnode), Error eNFile)
  | Success (afs, vnode) => do
  r <- read_afs_inode afs (v_ino parentdir);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa name) -> v_ino vnode)) dir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success dir => do
  r <- select (Success ` {sz. sz > v_size parentdir}) TODO: Alt return (Error eOverflow);
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success newsz => do
  time <- return (v_ctime vnode);
  vnode <- return (vnode <| v_size := ucast $ wordarray_length symname |>);
  dir <- return (dir <| i_ctime := time;
  i_mtime := time;
  i_size := v_size vnode |>);
  inode <- return (afs_inode_from_vnode vnode);
  inode <- return (i_path_update (\_. ALPHAwa symname) inode);
  (afs, r) <- afs_update afs (\f. f ((i_ino inode) -> inode, (i_ino dir) -> dir));
  (case r of
  | Error e => return ((afs, parentdir, vnode), Error e)
  | Success () => return ((afs, parentdir <| v_ctime := time;
  v_mtime := time;
  v_size := newsz |>, vnode), Success ()))
  od)
  od)
  od)
  od)
  od))
End

Definition pad_block_def:
  pad_block data len = data @ drop (length data) (replicate (unat len) 0)
End

Definition afs_readpage_def:
  afs_readpage afs vnode block buf = (if block > v_size vnode >> unat bilbyFsBlockShift then return ((afs, vnode, WordArrayT.make (replicate (unat bilbyFsBlockSize) 0)), Error eNoEnt) else (if block = v_size vnode >> unat bilbyFsBlockShift /\ v_size vnode mod (ucast bilbyFsBlockSize) = 0 then return ((afs, vnode, buf), Success ()) else do
  err <- {eIO;
  eNoMem;
  eInval;
  eBadF;
  eNoEnt};
  return ((afs, vnode, WordArrayT.make (pad_block (i_data (the $ updated_afs afs (v_ino vnode)) ! (unat block)) bilbyFsBlockSize)), Success ()) TODO: Alt return ((afs, vnode, buf), Error err)
  od))
End

Definition afs_write_begin_def:
  afs_write_begin afs vnode pos len buf = (if a_is_readonly afs then return ((afs, vnode, buf), Error eRoFs) else do
  ((afs, vnode, buf'), r) <- afs_readpage afs vnode (pos >> unat bilbyFsBlockShift) buf;
  (case r of
  | Error e => return ((afs, vnode, buf'), (if (e = eNoEnt) then Success () else Error e))
  | Success () => return ((afs, vnode, buf'), Success ()))
  od)
End

Definition afs_write_end_def:
  afs_write_end afs vnode pos len addr = (if a_is_readonly afs then return ((afs, vnode), Error eRoFs) else do
  newsize <- return (max (v_size vnode) (pos + ucast len));
  (afs, time) <- afs_get_current_time afs;
  vnode' <- return (vnode <| v_size := newsize;
  v_mtime := time |>);
  block <- return (unat $ pos >> unat bilbyFsBlockShift);
  (afs, r) <- afs_update afs (\f. f ((v_ino vnode) -> i_data_update (\data. data [block |-> ALPHAwa addr]) (the $ f (v_ino vnode)) <| i_size := newsize |>));
  (case r of
  | Error e => return ((afs, vnode), Error e)
  | Success () => return ((afs, vnode'), Success ()))
  od)
End

Definition afs_evict_inode_def:
  afs_evict_inode afs vnode = (if a_is_readonly afs then return (afs, Error eRoFs) else (if v_nlink vnode <> 0 then return (afs, Success ()) else afs_update afs (\f. f ((v_ino vnode) |-> None))))
End

Definition afs_follow_link_def:
  afs_follow_link afs vnode path = do
  r <- read_afs_inode afs (v_ino vnode);
  (case r of
  | Error e => return ((afs, vnode, path), Error e)
  | Success inode => let wa_path = WordArrayT.make (i_path inode);
  updated_path = wordarray_copy (path, wa_path, 0, 0, ucast (i_size inode))
  in
  return ((afs, vnode, updated_path), Success ()))
  od
End

Definition afs_rename_def:
  afs_rename afs vdir oldname oldvnode newname onewvnode = (if a_is_readonly afs then return ((afs, vdir, oldvnode, onewvnode), Error eRoFs) else do
  old_is_dir <- return (S_ISDIR (v_mode oldvnode));
  ncnt <- return (if old_is_dir then (v_nlink oldvnode - 1) else (v_nlink oldvnode));
  oldvnode' <- return (oldvnode <| v_nlink := ncnt |>);
  oldinode <- return ((the $ updated_afs afs (v_ino oldvnode)) <| i_nlink := ncnt |>);
  (afs, time) <- afs_get_current_time afs;
  newsz <- select UNIV;
  r <- read_afs_inode afs (v_ino vdir);
  (case r of
  | Error e => return ((afs, vdir, oldvnode, onewvnode), Error e)
  | Success dir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa oldname) |-> None, (ALPHAwa newname) |-> Some (v_ino oldvnode))) dir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, vdir, oldvnode, onewvnode), Error e)
  | Success dir => do
  dir <- return (dir <| i_ctime := time;
  i_mtime := time;
  i_size := newsz |>);
  (case onewvnode of
  | Some newvnode => let newinode = the $ updated_afs afs (v_ino newvnode);
  new_is_dir = afs_inode_is_dir (i_type newinode)
  in
  (if new_is_dir /\ dom (i_dir newinode) <> {} then return ((afs, vdir, oldvnode, onewvnode), Error eNotEmpty) else do
  ncnt <- return (if new_is_dir then 0 else (v_nlink newvnode - 1));
  newvnode' <- return (newvnode <| v_nlink := ncnt |>);
  newinode <- return (newinode <| i_nlink := ncnt |>);
  (afs, r) <- afs_update afs (\f. f ((i_ino oldinode) -> oldinode, (i_ino dir) -> dir, (i_ino newinode) -> newinode));
  (case r of
  | Error e => return ((afs, vdir, oldvnode, onewvnode), Error e)
  | Success () => let vdir' = vdir <| v_mtime := time;
  v_ctime := time;
  v_size := newsz |>
  in
  return ((afs, vdir', oldvnode', Some newvnode'), Success ()))
  od)
  | None => do
  (afs, r) <- afs_update afs (\f. f ((i_ino oldinode) -> oldinode, (i_ino dir) -> dir));
  (case r of
  | Error e => return ((afs, vdir, oldvnode, onewvnode), Error e)
  | Success () => let vdir' = vdir <| v_mtime := time;
  v_ctime := time;
  v_size := newsz |>
  in
  return ((afs, vdir', oldvnode', None), Success ()))
  od)
  od)
  od)
  od)
End

Definition afs_move_def:
  afs_move afs oldvdir oldname oldvnode newvdir newname onewvnode = (if a_is_readonly afs then return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error eRoFs) else do
  old_is_dir <- return (S_ISDIR (v_mode oldvnode));
  ncnt <- return (if old_is_dir then (v_nlink oldvnode - 1) else (v_nlink oldvnode));
  oldvnode' <- return (oldvnode <| v_nlink := ncnt |>);
  oldinode <- return ((the $ updated_afs afs (v_ino oldvnode)) <| i_nlink := ncnt |>);
  (afs, time) <- afs_get_current_time afs;
  r <- read_afs_inode afs (v_ino oldvdir);
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success olddir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa oldname) |-> None, (ALPHAwa newname) |-> Some (v_ino oldvnode))) olddir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success olddir => do
  onewsz <- select {sz. sz < v_size oldvdir};
  olddir <- return (olddir <| i_ctime := time;
  i_mtime := time;
  i_size := onewsz |>);
  oldvdir' <- return (oldvdir <| v_mtime := time;
  v_ctime := time;
  v_size := onewsz |>);
  r <- read_afs_inode afs (v_ino newvdir);
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success newdir => do
  r <- return (Success $ i_dir_update (\d. d ((ALPHAwa newname) |-> Some (v_ino oldvnode))) newdir) TODO: Alt return (Error eNameTooLong);
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success newdir => do
  nnewsz <- select {sz. sz > v_size newvdir};
  ncnt <- return (if old_is_dir then (v_nlink newvdir + 1) else (v_nlink newvdir));
  newvdir' <- return (newvdir <| v_ctime := time;
  v_mtime := time;
  v_nlink := ncnt;
  v_size := nnewsz |>);
  newdir <- return (newdir <| i_ctime := time;
  i_mtime := time;
  i_nlink := ncnt;
  i_size := nnewsz |>);
  (case onewvnode of
  | Some newvnode => let newinode = the $ updated_afs afs (v_ino newvnode);
  new_is_dir = afs_inode_is_dir (i_type newinode)
  in
  (if new_is_dir /\ dom (i_dir newinode) <> {} then return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error eNotEmpty) else do
  ncnt <- return (if new_is_dir then 0 else (v_nlink newvnode - 1));
  newvnode' <- return (newvnode <| v_nlink := ncnt |>);
  newinode <- return (newinode <| i_nlink := ncnt |>);
  (afs, r) <- afs_update afs (\f. f ((i_ino oldinode) -> oldinode, (i_ino olddir) -> olddir, (i_ino newdir) -> newdir, (i_ino newinode) -> newinode));
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success () => return ((afs, oldvdir', oldvnode', newvdir', Some newvnode'), Success ()))
  od)
  | None => do
  (afs, r) <- afs_update afs (\f. f ((i_ino oldinode) -> oldinode, (i_ino olddir) -> olddir, (i_ino newdir) -> newdir));
  (case r of
  | Error e => return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
  | Success () => return ((afs, oldvdir', oldvnode', newvdir', None), Success ()))
  od)
  od)
  od)
  od)
  od)
  od)
End

Definition afs_dir_emit_def:
  afs_dir_emit = \(pos, entries) name ino vtype. do
  bool <- select UNIV;
  (if bool then return (Iterate (pos, entries ((ALPHAwa name) |-> None))) else return (Break (pos, entries ((ALPHAwa name) |-> None))))
  od
End

Definition afs_readdir_def:
  afs_readdir afs rdctx obrdctx vdir = do
  r <- read_afs_inode afs (v_ino vdir);
  (case r of
  | Error e => return ((afs, rdctx, obrdctx), Error e)
  | Success dir => do
  toemit <- select {entries. entries SUBSET dom (i_dir dir)};
  obrdctx <- select UNIV;
  pos <- select UNIV;
  return ((afs, (pos, (snd rdctx) |` (-toemit)), obrdctx), Success ())
  od)
  od
End

Datatype:
vfsstat = <|
  vs_ino :  Ino;
  vs_nlink :  U32;
  vs_mode :  Mode;
  vs_uid :  U32;
  vs_gid :  U32;
  vs_size :  U64;
  vs_atime :  TimeT;
  vs_mtime :  TimeT;
  vs_ctime :  TimeT;
  vs_blksize :  U32;
  vs_blocks :  U32
|>
End


Definition afs_getattr_def:
  afs_getattr afs stat vnode = return (afs, stat <| vs_ino := v_ino vnode;
  vs_nlink := v_nlink vnode;
  vs_mode := v_mode vnode;
  vs_uid := v_uid vnode;
  vs_gid := v_gid vnode;
  vs_size := v_size vnode;
  vs_atime := v_mtime vnode;
  vs_mtime := v_mtime vnode;
  vs_ctime := v_ctime vnode;
  vs_blksize := bilbyFsBlockSize;
  vs_blocks := ucast (v_size vnode) div 512 + (if (v_size vnode mod 512 > 0) then 1 else 0) |>)
End

Datatype:
iattr = <|
  iattr_valid :  U32;
  iattr_mode :  Mode;
  iattr_uid :  U32;
  iattr_gid :  U32;
  iattr_mtime :  TimeT;
  iattr_ctime :  TimeT
|>
End


Definition iattr_is_set_def:
  iattr_is_set iattr flag = iattr_valid iattr AND flag <> 0
End

Definition afs_setattr_def:
  afs_setattr afs iattr vnode = let vnode' = (if iattr_is_set iattr vfs_ATTR_MODE then vnode <| v_mode := iattr_mode iattr |> else vnode);
  vnode' = (if iattr_is_set iattr vfs_ATTR_UID then vnode' <| v_uid := iattr_uid iattr |> else vnode');
  vnode' = (if iattr_is_set iattr vfs_ATTR_GID then vnode' <| v_gid := iattr_gid iattr |> else vnode');
  vnode' = (if iattr_is_set iattr vfs_ATTR_MTIME then vnode' <| v_mtime := iattr_mtime iattr |> else vnode');
  vnode' = (if iattr_is_set iattr vfs_ATTR_CTIME then vnode' <| v_ctime := iattr_ctime iattr |> else vnode')
  in
  do
  (afs, r) <- afs_update afs (\f. f ((v_ino vnode') -> the (f (v_ino vnode')) <| i_mode := v_mode vnode';
  i_uid := v_uid vnode';
  i_gid := v_gid vnode';
  i_mtime := v_mtime vnode';
  i_ctime := v_ctime vnode' |>));
  (case r of
  | Error e => return ((afs, vnode), Error e)
  | Success () => return ((afs, vnode'), Success ()))
  od
End

val _ = export_theory ()
