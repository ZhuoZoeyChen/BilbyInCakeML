theory testFile

imports Main

begin


definition "a = select {x. x \<ge> time'}"

(afs, r) <- afs_update afs (\f. f(dir_ino |-> (i_dir_update (\d. d(name:=option.None)) (the $ f dir_ino)\<lparr>i_ctime:=time,i_mtime:=time\<rparr>),
                                            v_ino vnode \<mapsto> inode));

end