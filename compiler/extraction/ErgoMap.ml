open Ast
open Datatypes
open Ergo
open List0
open Misc
open Result0

(** val ergo_map_expr :
    ('a4 -> char list -> ('a1, 'a2, 'a3) ergo_expr -> 'a4) -> ('a4 -> ('a1,
    'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult option) -> 'a4
    -> ('a1, 'a2, 'a3) ergo_expr -> ('a1, 'a2, 'a3) ergo_expr eresult **)

let rec ergo_map_expr ctxt_new_variable_scope fn ctx expr =
  let maybe_fn = elift_maybe (fn ctx) in
  let apply_map = ergo_map_expr ctxt_new_variable_scope fn in
  maybe_fn
    (match expr with
     | EText (loc, a) ->
       elift (fun x -> EText (loc, x))
         (fold_left (fun ls na -> elift2 postpend ls (apply_map ctx na)) a
           (esuccess [] []))
     | ESome (loc, e) -> elift (fun x -> ESome (loc, x)) (apply_map ctx e)
     | EArray (loc, a) ->
       elift (fun x -> EArray (loc, x))
         (fold_left (fun ls na -> elift2 postpend ls (apply_map ctx na)) a
           (esuccess [] []))
     | EUnaryOperator (loc, o, e) ->
       elift (fun x -> EUnaryOperator (loc, o, x)) (apply_map ctx e)
     | EBinaryOperator (loc, o, e1, e2) ->
       elift2 (fun x x0 -> EBinaryOperator (loc, o, x, x0))
         (apply_map ctx e1) (apply_map ctx e2)
     | EUnaryBuiltin (loc, o, e) ->
       elift (fun x -> EUnaryBuiltin (loc, o, x)) (apply_map ctx e)
     | EBinaryBuiltin (loc, o, e1, e2) ->
       elift2 (fun x x0 -> EBinaryBuiltin (loc, o, x, x0)) (apply_map ctx e1)
         (apply_map ctx e2)
     | EIf (loc, c, t, f) ->
       elift3 (fun x x0 x1 -> EIf (loc, x, x0, x1)) (apply_map ctx c)
         (apply_map ctx t) (apply_map ctx f)
     | ELet (loc, n, t, v, b) ->
       elift2 (fun v' b' -> ELet (loc, n, t, v', b')) (apply_map ctx v)
         (apply_map (ctxt_new_variable_scope ctx n v) b)
     | EPrint (loc, v, b) ->
       elift2 (fun v' b' -> EPrint (loc, v', b')) (apply_map ctx v)
         (apply_map ctx b)
     | ERecord (loc, rs) ->
       elift (fun x -> ERecord (loc, x))
         (fold_left (fun ls nr ->
           elift2 postpend ls
             (elift (fun x -> ((fst nr), x)) (apply_map ctx (snd nr)))) rs
           (esuccess [] []))
     | ENew (loc, n, rs) ->
       elift (fun x -> ENew (loc, n, x))
         (fold_left (fun ls nr ->
           elift2 postpend ls
             (elift (fun x -> ((fst nr), x)) (apply_map ctx (snd nr)))) rs
           (esuccess [] []))
     | ECallFun (loc, fn', args) ->
       elift (fun x -> ECallFun (loc, fn', x))
         (fold_left (fun ls nv -> elift2 postpend ls (apply_map ctx nv)) args
           (esuccess [] []))
     | ECallFunInGroup (loc, gn, fn', args) ->
       elift (fun x -> ECallFunInGroup (loc, gn, fn', x))
         (fold_left (fun ls nv -> elift2 postpend ls (apply_map ctx nv)) args
           (esuccess [] []))
     | EMatch (loc, expr0, pes, def) ->
       eolift (fun expr' ->
         eolift (fun def' ->
           elift (fun pes' -> EMatch (loc, expr', pes', def'))
             (fold_right (fun pe prev ->
               elift2 (fun pe' prev' -> pe' :: prev')
                 (let (y, e) = pe in
                  (match y with
                   | CaseLet (_, name, _) ->
                     elift (fun x -> ((fst pe), x))
                       (ergo_map_expr ctxt_new_variable_scope fn
                         (ctxt_new_variable_scope ctx name expr') e)
                   | CaseLetOption (_, name, _) ->
                     elift (fun x -> ((fst pe), x))
                       (ergo_map_expr ctxt_new_variable_scope fn
                         (ctxt_new_variable_scope ctx name expr') e)
                   | _ -> elift (fun x -> ((fst pe), x)) (apply_map ctx e)))
                 prev) (esuccess [] []) pes)) (apply_map ctx def))
         (apply_map ctx expr0)
     | EForeach (loc, rs, whr, r) ->
       let rs_ctx' =
         let proc_one = fun ctx0 nr ->
           let (n, e) = nr in
           elift (fun x -> (x, (ctxt_new_variable_scope ctx0 n e)))
             (elift (fun x -> (n, x)) (apply_map ctx0 e))
         in
         elift_context_fold_left proc_one rs ctx
       in
       eolift (fun xy ->
         let (rs', ctx0) = xy in
         let whr' =
           match whr with
           | Some whr' -> elift (fun x -> Some x) (apply_map ctx0 whr')
           | None -> esuccess None []
         in
         let r' = apply_map ctx0 r in
         elift3 (fun x x0 x1 -> EForeach (loc, x, x0, x1)) (esuccess rs' [])
           whr' r') rs_ctx'
     | EAs (loc, f, e) -> elift (fun x -> EAs (loc, f, x)) (apply_map ctx e)
     | _ -> esuccess expr [])
