theory testFile
imports "../lib/FunBucket"
"../adt/VfsT"
"../adt/WordArrayT"
"../lib/CogentMonad"
begin

definition
  nondet_error :: " ErrCode set \<Rightarrow> ( ErrCode \<Rightarrow> 'a) \<Rightarrow> 'a cogent_monad"
where
  "nondet_error errs (f (a := b))"

end
