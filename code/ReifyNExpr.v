(* Note from Dan: my comments in the code are prefixed with `DF'. *)
Require Import Coq.Strings.String.
Require Import MetaCoq.Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.
Require Import EvalNExpr.

Definition NExpr_term_equiv (Γ: evalContext) (d: NExpr) (s: nat) : Prop :=
  evalNexp Γ d = Some s.

Run TemplateProgram (mkSwitch string
                              eq_string
                              [("Coq.Init.Nat.add", "n_Add") ;
                                 ("Coq.Init.Nat.sub", "n_Sub") ;
                                 ("Coq.Init.Nat.mul", "n_Mul")]
                              "NOp_Names" "parse_NOp_Name").

(* DF: to see what did the previous command do:
Print NOp_Names.
Check parse_NOp_Name.
Eval compute in (parse_NOp_Name "Coq.Init.Nat.add"). *)

Definition inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat";
                       inductive_ind := 0 |}.
Definition nt := tInd inat [].
(* DF:
Check inat.
Check nt. *)
Definition ilist := {| inductive_mind := "Coq.Init.Datatypes.list";
                       inductive_ind := 0 |}.

Definition varlist:Type := list string.

Fixpoint compileNExpr (params:varlist) (a_n:term): TemplateMonad (varlist*NExpr) :=
  match a_n with
  (* Case 0 *)
  | tConstruct inat 0 [] => tmReturn (params, NConst 0)
  (* Case (S e) *)
  | tApp (tConstruct inat 1 []) [e] =>
    d_e <- compileNExpr params e ;;
        let '(_, d_e') := d_e in
        tmReturn (params, (match d_e' with
                           | NConst v => NConst (S v)
                           | o => NPlus o (NConst 1)
                           end))
  (* Case binary function f (a_a, a_b) *)
  | tApp (tConst bfun []) [ a_a ; a_b] =>
    d_a <- compileNExpr params a_a ;;
    d_b <- compileNExpr params a_b ;;
    let '(_, d_a') := d_a in
    let '(_, d_b') := d_b in
    match parse_NOp_Name bfun with
    | Some n_Add => tmReturn (params, NPlus  d_a' d_b')
    | Some n_Sub => tmReturn (params, NMinus d_a' d_b')
    | Some n_Mul => tmReturn (params, NMult  d_a' d_b')
    | None => tmFail ("Unknown binary function" ++ bfun)
    end
  (* The last two cases are for dealing with variables *)
  | tLambda (nNamed n) nt b_n =>  compileNExpr (n::params) b_n
  | tRel n => tmReturn (params, NVar n)
  | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
  end.

(* DF: using compileNExpr :
Definition test_compileNExpr (t : term) : TemplateMonad unit :=
  r <- compileNExpr [] t ;;
  let '(params, res) := r in
  nres <- tmEval all res ;;
  tmPrint params ;;
  tmPrint res ;;
  tmPrint nres.

Quote Definition test1 := (1 + 0).
Quote Definition test2 := (fun x => x * (0 + 1)).
Run TemplateProgram ( test_compileNExpr test1 ).
Run TemplateProgram ( test_compileNExpr test2 ).
*)

Fixpoint build_param_list (l:varlist) : TemplateMonad term :=
  match l with
  | [] => tmReturn (tApp (tConstruct ilist 0 []) [nt])
  | x::xs => ts <- build_param_list xs ;;
             tmReturn (tApp (tConstruct ilist 1 []) [nt; tRel (length xs); ts])
  end.

Definition build_forall (p:varlist) conc :=
  fold_right (fun n ps => tProd (nNamed n) nt ps) conc p.

Polymorphic Definition reifyNExp {A:Type}
            (res_name: string)
            (lemma_name: string)
            (nexpr:A):
  TemplateMonad unit :=
  e <- tmEval cbv nexpr ;;
  ast <- tmQuote e ;;
  cast <- compileNExpr [] ast ;;
  let '(params, c) := cast in
  c' <- tmEval cbv c ;; (* extra cbv to fold nat constructors *)
  (* definition with resuting NExpr *)
  def <- tmDefinition res_name c' ;;
  (* lemma *)
  a_params <- build_param_list params ;;
  let param_idx := map tRel (seq 0 (length params)) in
  let a_exp := tApp ast param_idx in
  a_c <- tmQuote c' ;;
  let lemma_concl := tApp (tConst "NExpr_term_equiv" []) [a_params; a_c; a_exp] in
  let lemma_ast := build_forall params lemma_concl in
  (tmBind (tmUnquoteTyped Prop lemma_ast)
          (fun lemma_body => _ <- tmLemma lemma_name lemma_body ;;
                             tmReturn tt)).

(* DF: example usage
Run TemplateProgram (reifyNExp "e1" "e1_correct" (2 + 1 * 0)).
Next Obligation. vm_compute; reflexivity. Qed.
Print e1.
Check e1_correct.
*)

(* DF: This is a more complicated example, where we cannot just solve
the goal by `reflexivity':

Run TemplateProgram (reifyNExp "e2" "e2_correct" (fun (x : nat) => 2 + x)).
Next Obligation.
  unfold NExpr_term_equiv. simpl.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite <- (plus_n_O x).
  rewrite <- (plus_n_O (S x)).
  reflexivity.
Qed.
Print e2.
Check e2_correct.
*)

(* -- Proof automation  -- *)

Lemma NExpr_add_equiv (σ: evalContext) {a b a' b'}:
  NExpr_term_equiv σ a a' ->
  NExpr_term_equiv σ b b' ->
  NExpr_term_equiv σ (NPlus a b) (Nat.add a' b').
Proof.
  intros Ha Hb.
  unfold NExpr_term_equiv in *.
  simpl.
  rewrite Ha, Hb.
  reflexivity.
Qed.


Lemma NExpr_mul_equiv (σ: evalContext) {a b a' b'}:
  NExpr_term_equiv σ a a' ->
  NExpr_term_equiv σ b b' ->
  NExpr_term_equiv σ (NMult a b) (Nat.mul a' b').
Proof.
  intros Ha Hb.
  unfold NExpr_term_equiv in *.
  simpl.
  rewrite Ha, Hb.
  reflexivity.
Qed.

Lemma NExpr_const_equiv (σ: evalContext) {v v'}:
  evalNexp σ (NConst v) = Some v' ->
  NExpr_term_equiv σ (NConst v) v'.
Proof.
  intros H.
  auto.
Qed.

Lemma NExpr_var_equiv (σ: evalContext) {v x}:
  evalNexp σ (NVar v) = Some x ->
  NExpr_term_equiv σ (NVar v) x.
Proof.
  intros H.
  unfold NExpr_term_equiv in *.
  simpl in *.
  apply H.
Qed.

Create HintDb NExprHints.
Hint Resolve NExpr_add_equiv NExpr_mul_equiv: NExprHints.
Hint Resolve NExpr_const_equiv NExpr_var_equiv: NExprHints.

(* --- Reification example --- *)

Example Ex1 (a b c: nat) := fun x => 2 + a*x*x + b*x + c.


Opaque Nat.add Nat.sub Nat.mul.
(* In this example obligations could be solved with `reflexivity` but
   for demonstration purposes we solve it by automation *)
Obligation Tactic := intros; simpl; eauto 99 with NExprHints.
Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).

Print Ex1_def.
Check Ex1_lemma.

(* DF: as an exercise, what would be needed to implement
      things like let binding in this embedded language? *)
