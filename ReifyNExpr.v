Require Import Coq.Strings.String.
Require Import Template.All.
Require Import Switch.Switch.
Require Import Coq.Lists.List.

Import MonadNotation.
Import ListNotations.

Require Import NExpr.

Set Universe Polymorphism.
Set Printing Universes.

Example Ex1 (a b c x: nat) := 2 + a*x*x + b*x + c.

Definition string_beq a b := if string_dec a b then true else false.

Run TemplateProgram
    (mkSwitch string
              string_beq
              [("Coq.Init.Nat.add", "n_Add") ;
                 ("Coq.Init.Nat.sub", "n_Sub") ;
                 ("Coq.Init.Nat.mul", "n_Mul")]
              "NOp_Names" "parse_NOp_Name"
    ).

Section Reify.
  Local Opaque Nat.add Nat.sub Nat.mul.

  Fixpoint compileNExpr (nparam:nat) (a_n:term): TemplateMonad (nat*NExpr) :=
    let inat :=  {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} in
    match a_n with
    | (tConstruct inat 0 []) => tmReturn (nparam, NConst 0)
    | (tApp (tConstruct inat 1 []) [e]) =>
      d_e <- compileNExpr nparam e ;;
          let '(_, d_e') := d_e in
          tmReturn (nparam, (match d_e' with
                             | NConst v => NConst (v+1)
                             | o => NPlus o (NConst 1)
                             end))
    | (tApp (tConst bfun []) [ a_a ; a_b]) =>
      d_a <- compileNExpr nparam a_a ;;
          d_b <- compileNExpr nparam a_b ;;
          let '(_, d_a') := d_a in
          let '(_, d_b') := d_b in
          match parse_NOp_Name bfun with
          | Some n_Add => tmReturn (nparam, NPlus d_a' d_b')
          | Some n_Sub => tmReturn (nparam, NMinus d_a' d_b')
          | Some n_Mul => tmReturn (nparam, NMult d_a' d_b')
          | None => tmFail ("Unknown binary function" ++ bfun)
          end
    | (tLambda _ (tInd inat []) b_n) =>  compileNExpr (nparam+1) b_n
    | tRel n => tmReturn (nparam, NVar n)
    | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
    end.

  Definition reifyNExp@{t u} {A:Type@{t}}
             (res_name: string)
             (lemma_name: string)
             (nexpr:A):
    TemplateMonad@{t u} unit :=
    nn <- tmQuote nexpr ;;
       match nn with
       | tConst name [] =>
         e <- tmEval (unfold "Ex1") nexpr ;; (* TODO: strip `name` up to last '.' *)
           ast <- tmQuote e ;;
           cast <- compileNExpr 0 ast ;;
           let '(nparam, c) := cast in
           c' <- tmEval cbv c ;;
           def <- tmDefinition res_name c' ;;
           tmPrint nparam ;;
           tmPrint c' ;;
           tmReturn tt
       | _ => tmFail "unexpected parameter type"
       end.

  Run TemplateProgram (reifyNExp "Ex1_def" "Ex1_lemma" Ex1).

  Print Ex1_def.

End Reify.
