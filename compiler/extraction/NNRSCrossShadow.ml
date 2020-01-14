open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open Fresh
open Lift
open List0
open NNRS
open NNRSRename
open NNRSVars
open Var

(** val nnrs_stmt_uncross_shadow_under :
    foreign_runtime -> char list -> nnrs_stmt -> var list -> var list -> var
    list -> nnrs_stmt **)

let rec nnrs_stmt_uncross_shadow_under fruntime sep s _UU03c3_ _UU03c8_c _UU03c8_d =
  match s with
  | NNRSSeq (s_UU2081_, s_UU2082_) ->
    NNRSSeq
      ((nnrs_stmt_uncross_shadow_under fruntime sep s_UU2081_ _UU03c3_
         _UU03c8_c _UU03c8_d),
      (nnrs_stmt_uncross_shadow_under fruntime sep s_UU2082_ _UU03c3_
        _UU03c8_c _UU03c8_d))
  | NNRSLet (v, e, s_UU2080_) ->
    let s_UU2080_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2080_ (v :: _UU03c3_)
        _UU03c8_c _UU03c8_d
    in
    let problems =
      app
        (remove (equiv_dec string_eqdec) v
          (nnrs_stmt_free_env_vars fruntime s_UU2080_'))
        (app
          (remove (equiv_dec string_eqdec) v
            (nnrs_stmt_bound_env_vars fruntime s_UU2080_'))
          (app (nnrs_stmt_free_mcenv_vars fruntime s_UU2080_')
            (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2080_')
              (app (nnrs_stmt_free_mdenv_vars fruntime s_UU2080_')
                (nnrs_stmt_bound_mdenv_vars fruntime s_UU2080_')))))
    in
    let v' = fresh_var_from sep v problems in
    NNRSLet (v', e,
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2080_' v
      v'))
  | NNRSLetMut (v, s_UU2081_, s_UU2082_) ->
    let s_UU2081_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2081_ _UU03c3_
        _UU03c8_c (v :: _UU03c8_d)
    in
    let s_UU2082_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2082_ (v :: _UU03c3_)
        _UU03c8_c _UU03c8_d
    in
    let problems =
      app
        (remove (equiv_dec string_eqdec) v
          (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_'))
        (app
          (remove (equiv_dec string_eqdec) v
            (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_'))
          (app
            (remove (equiv_dec string_eqdec) v
              (nnrs_stmt_free_env_vars fruntime s_UU2082_'))
            (app
              (remove (equiv_dec string_eqdec) v
                (nnrs_stmt_bound_env_vars fruntime s_UU2082_'))
              (app _UU03c3_
                (app _UU03c8_d
                  (app (nnrs_stmt_free_env_vars fruntime s_UU2081_')
                    (app (nnrs_stmt_bound_env_vars fruntime s_UU2081_')
                      (app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_')
                        (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_')
                          (app
                            (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_')
                            (app
                              (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_')
                              (app
                                (nnrs_stmt_free_mdenv_vars fruntime
                                  s_UU2082_')
                                (nnrs_stmt_bound_mdenv_vars fruntime
                                  s_UU2082_')))))))))))))
    in
    let v' = fresh_var_from sep v problems in
    NNRSLetMut (v',
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_md fruntime) s_UU2081_' v v'),
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2082_' v
      v'))
  | NNRSLetMutColl (v, s_UU2081_, s_UU2082_) ->
    let s_UU2081_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2081_ _UU03c3_
        (v :: _UU03c8_c) _UU03c8_d
    in
    let s_UU2082_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2082_ (v :: _UU03c3_)
        _UU03c8_c _UU03c8_d
    in
    let problems =
      app
        (remove (equiv_dec string_eqdec) v
          (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_'))
        (app
          (remove (equiv_dec string_eqdec) v
            (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_'))
          (app
            (remove (equiv_dec string_eqdec) v
              (nnrs_stmt_free_env_vars fruntime s_UU2082_'))
            (app
              (remove (equiv_dec string_eqdec) v
                (nnrs_stmt_bound_env_vars fruntime s_UU2082_'))
              (app _UU03c3_
                (app _UU03c8_d
                  (app _UU03c8_c
                    (app (nnrs_stmt_free_env_vars fruntime s_UU2081_')
                      (app (nnrs_stmt_bound_env_vars fruntime s_UU2081_')
                        (app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_')
                          (app
                            (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_')
                            (app
                              (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_')
                              (app
                                (nnrs_stmt_bound_mcenv_vars fruntime
                                  s_UU2082_')
                                (app
                                  (nnrs_stmt_free_mdenv_vars fruntime
                                    s_UU2082_')
                                  (nnrs_stmt_bound_mdenv_vars fruntime
                                    s_UU2082_'))))))))))))))
    in
    let v' = fresh_var_from sep v problems in
    NNRSLetMutColl (v',
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_mc fruntime) s_UU2081_' v v'),
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2082_' v
      v'))
  | NNRSFor (v, e, s_UU2080_) ->
    let s_UU2080_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2080_ (v :: _UU03c3_)
        _UU03c8_c _UU03c8_d
    in
    let problems =
      app
        (remove (equiv_dec string_eqdec) v
          (nnrs_stmt_free_env_vars fruntime s_UU2080_'))
        (app
          (remove (equiv_dec string_eqdec) v
            (nnrs_stmt_bound_env_vars fruntime s_UU2080_'))
          (app (nnrs_stmt_free_mcenv_vars fruntime s_UU2080_')
            (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2080_')
              (app (nnrs_stmt_free_mdenv_vars fruntime s_UU2080_')
                (nnrs_stmt_bound_mdenv_vars fruntime s_UU2080_')))))
    in
    let v' = fresh_var_from sep v problems in
    NNRSFor (v', e,
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2080_' v
      v'))
  | NNRSIf (e, s_UU2081_, s_UU2082_) ->
    NNRSIf (e,
      (nnrs_stmt_uncross_shadow_under fruntime sep s_UU2081_ _UU03c3_
        _UU03c8_c _UU03c8_d),
      (nnrs_stmt_uncross_shadow_under fruntime sep s_UU2082_ _UU03c3_
        _UU03c8_c _UU03c8_d))
  | NNRSEither (e, x_UU2081_, s_UU2081_, x_UU2082_, s_UU2082_) ->
    let s_UU2081_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2081_
        (x_UU2081_ :: _UU03c3_) _UU03c8_c _UU03c8_d
    in
    let problems_UU2081_ =
      app
        (remove (equiv_dec string_eqdec) x_UU2081_
          (nnrs_stmt_free_env_vars fruntime s_UU2081_'))
        (app
          (remove (equiv_dec string_eqdec) x_UU2081_
            (nnrs_stmt_bound_env_vars fruntime s_UU2081_'))
          (app (nnrs_stmt_free_mcenv_vars fruntime s_UU2081_')
            (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2081_')
              (app (nnrs_stmt_free_mdenv_vars fruntime s_UU2081_')
                (nnrs_stmt_bound_mdenv_vars fruntime s_UU2081_')))))
    in
    let x_UU2081_' = fresh_var_from sep x_UU2081_ problems_UU2081_ in
    let s_UU2082_' =
      nnrs_stmt_uncross_shadow_under fruntime sep s_UU2082_
        (x_UU2082_ :: _UU03c3_) _UU03c8_c _UU03c8_d
    in
    let problems_UU2082_ =
      app
        (remove (equiv_dec string_eqdec) x_UU2082_
          (nnrs_stmt_free_env_vars fruntime s_UU2082_'))
        (app
          (remove (equiv_dec string_eqdec) x_UU2082_
            (nnrs_stmt_bound_env_vars fruntime s_UU2082_'))
          (app (nnrs_stmt_free_mcenv_vars fruntime s_UU2082_')
            (app (nnrs_stmt_bound_mcenv_vars fruntime s_UU2082_')
              (app (nnrs_stmt_free_mdenv_vars fruntime s_UU2082_')
                (nnrs_stmt_bound_mdenv_vars fruntime s_UU2082_')))))
    in
    let x_UU2082_' = fresh_var_from sep x_UU2082_ problems_UU2082_ in
    NNRSEither (e, x_UU2081_',
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2081_'
      x_UU2081_ x_UU2081_'), x_UU2082_',
    (mk_lazy_lift string_eqdec (nnrs_stmt_rename_env fruntime) s_UU2082_'
      x_UU2082_ x_UU2082_'))
  | x -> x

(** val nnrs_uncross_shadow : foreign_runtime -> char list -> nnrs -> nnrs **)

let nnrs_uncross_shadow fruntime sep s =
  let s' =
    nnrs_stmt_uncross_shadow_under fruntime sep (fst s) [] [] ((snd s) :: [])
  in
  let problems =
    app (nnrs_stmt_free_env_vars fruntime s')
      (app (nnrs_stmt_bound_env_vars fruntime s')
        (app (nnrs_stmt_free_mcenv_vars fruntime s')
          (app (nnrs_stmt_bound_mcenv_vars fruntime s')
            (app
              (remove (equiv_dec string_eqdec) (snd s)
                (nnrs_stmt_free_mdenv_vars fruntime s'))
              (remove (equiv_dec string_eqdec) (snd s)
                (nnrs_stmt_bound_mdenv_vars fruntime s'))))))
  in
  let v' = fresh_var_from sep (snd s) problems in
  ((mk_lazy_lift string_eqdec (nnrs_stmt_rename_md fruntime) s' (snd s) v'),
  v')
