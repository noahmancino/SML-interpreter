(*  Concrete syntax

e :: x | n | true | false | succ | pred | iszero | if e then e else e
       | fn x => e | e e | (e) | let x = e in e

*)
(* The following definition in in the parser module 
datatype term = AST_ID of string | AST_NUM of int  | AST_BOOL of bool| 
                AST_SUCC | AST_PRED | AST_ISZERO | AST_ADD |
                AST_IF of term * term * term | 
                AST_FUN of string * term | AST_APP of term * term| 
                AST_LET of (string * term * term)| AST_ERROR of string |
                AST_REC of (string * term)

*)

use "parser.sml";

datatype result = RES_ERROR of string | RES_NUM of int| RES_BOOL of bool |
                  RES_SUCC | RES_PRED | RES_ISZERO |
                  RES_FUN of ((string * term) * env)
and env = Env of (string -> result)

exception  Error of string
exception  UnboundID of string ;
exception Not_implemented

fun emptyenvFun  (x : string) : result = raise UnboundID x;

val emptyenv = Env emptyenvFun

fun look_up (Env e) x = e x 

(* e [x=v]  update e x v *)

(*  update : env -> string -> result -> string -> result  *)
fun update env (x : string) (value : result) =
                  fn y => if x = y then value else look_up env y

fun interp_static  (env, AST_SUCC)          = RES_SUCC
|   interp_static  (env, AST_PRED)          = RES_PRED
|   interp_static  (env, AST_ISZERO)        = RES_ISZERO
|   interp_static  (env, AST_NUM n)         = RES_NUM n
|   interp_static  (env, AST_BOOL b)        = RES_BOOL b
|   interp_static  (env, AST_ID x  )        = look_up env x 
|   interp_static  (env, AST_IF (e1,e2,e3)) = (case interp_static (env,e1) of
                            RES_BOOL true  => interp_static  (env,e2)
                          | RES_BOOL false => interp_static  (env,e3)
                          | _              => raise 
                                             (Error "if condition non-bool!") )

|   interp_static  (env, AST_FUN(x,body))   = let val unit = look_up env "x" val n = (case unit of RES_NUM n => n) val unit3 = print("\n" ^ Int.toString n ^ "\n\n")
in RES_FUN ((x,body), env) end
|   interp_static  (env, AST_LET (x,e1,e2)) = let val v1 = interp_static (env, e1)
                                        in interp_static (Env (update env x v1), e2)
                                       end

   
|  interp_static  (env, AST_APP(AST_APP(AST_ADD,e1),e2)) =  (* + e1 e2 *)
             (case interp_static (env, e1) of
                RES_NUM n1 => (case interp_static (env, e2) of
                                   RES_NUM n2 => RES_NUM (n1+n2)
                                  | _         => raise (Error "not a number"))
              | _          => raise (Error "not a number") 
                       )
| interp_static (env, AST_APP(AST_ADD,e1)) = raise (Error "not enough arguments for +") (* + e1 *)
| interp_static   (env, AST_APP (e1,e2))   =
       (case interp_static  (env, e1) of
         RES_FUN ((formal, body), closure) =>
                                  let val actual = interp_static (env, e2) 
                                                  val new_env = Env(update closure formal actual)
                                                  val unit1 = print("\n" ^ formal ^ "\n\n")
                                                  val unit2 = look_up closure "x"
                                                  val n = (case unit2 of RES_NUM n => n | _ => 0)
                                                  val unit4 = print("\n" ^ Int.toString n ^ "\n")
                                  in
                                  interp_static (new_env, body)
                                  end
       | RES_SUCC =>
         (case interp_static (env,e2) of
              RES_NUM n => RES_NUM (n+1)
            | _ => raise (Error "succ non-number"))
       | RES_PRED =>
         (case interp_static (env,e2) of
              RES_NUM n => RES_NUM (n+1)
            | _ => raise (Error "pred non-number"))
       | RES_ISZERO =>
         (case interp_static (env,e2) of
              RES_NUM n => RES_BOOL (n = 0)
            | _ => raise (Error "iszero non-number"))
       | _ => raise (Error "apply non-function") )
 |  interp_static (env, AST_ERROR s)       = raise (Error s)
 |  interp_static (env, _)                = raise Not_implemented;

interp_static(emptyenv,parsestr ("let x = 21 in let foo = fn y => x in let x = 13 in foo 0 end end end"));
