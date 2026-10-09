(** * The translation preserves typing

    If PCF checks [Γ ⊢ t ⇓ A] (the annotated, bidirectional system of
    strictness-pcf), then [t] is translated, and in U⁻ the translation
    checks against [⟦A⟧] in the translated context [⟦Γ⟧]:

      PCF  Γ ⊢ t ⇓ A    ⟹    U⁻  ⟦Γ⟧ ⊢ ⟦t⟧ ⇓ ⟦A⟧

    for every PCF-checked program ([translation_preserves_typing]).
    Conversely, whatever the translator outputs is typed this way
    ([translate_sound]).

    The ingredients:
    - the encodings are closed terms with typing certificates in the empty
      context, from checker runs and [run_infer_sound]; [synth_closed]
      carries them into any context;
    - translated types are closed, so lifting and substitution leave them
      unchanged, and they all synthesize ∗;
    - numerals are typed for every [k], by induction;
    - names: PCF's [lookup] finds the first entry, and so does the
      builder's [index_of]; the translated context holds closed types. *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Reduction Bidir Check CheckSound.
From DepTypes.Configs Require Import Finite.
From DepTypes.SystemU Require Import Looping Encodings.
From DepTypes.PCFTranslation Require Import Translate.
From PCF Require Ty Syntax Context Checker.

Notation tty := translated_type.

(** ** Closed constants and their certificates *)

Definition nat' : term := church CNat.
Definition bool' : term := church CBool.

Lemma nat'_form : nat' = Pi (Srt Star) (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2))).
Proof. reflexivity. Qed.

Lemma bool'_form : bool' = Pi (Srt Star) (Pi (Var 0) (Pi (Var 1) (Var 2))).
Proof. reflexivity. Qed.

Lemma looping_ty_form : looping_ty = Pi (Srt Star) (Pi (Pi (Var 0) (Var 1)) (Var 1)).
Proof. vm_compute. reflexivity. Qed.

(** A closed constant resolves to its [church] term under any names. *)
Lemma resolve_const : forall c ns, resolve [] c = Ok (church c) -> resolve ns c = Ok (church c).
Proof. intros c ns H. exact (resolve_closed c (church c) ns H). Qed.

Lemma resolve_CNat : resolve [] CNat = Ok nat'.
Proof. reflexivity. Qed.
Lemma resolve_csucc : resolve [] csucc = Ok (church csucc).
Proof. vm_compute. reflexivity. Qed.
Lemma resolve_cpred : resolve [] cpred = Ok (church cpred).
Proof. vm_compute. reflexivity. Qed.
Lemma resolve_is_zero : resolve [] is_zero = Ok (church is_zero).
Proof. vm_compute. reflexivity. Qed.
Lemma resolve_L0 : resolve [] L0 = Ok (looping 0).
Proof. vm_compute. reflexivity. Qed.

Lemma closed_church : forall c, resolve [] c = Ok (church c) -> closed (church c) = true.
Proof. intros c H. exact (resolve_closed_term c (church c) H). Qed.

(** Typing certificates in the empty context, carried into any. *)
Lemma certificate : forall G c A,
  typed_in_u_minus c A = true -> resolve [] c = Ok (church c) ->
  system_u_minus ;; G ⊢ church c ⇑ church A.
Proof.
  intros G c A Ht Hr. apply synth_closed; [ | exact (closed_church c Hr)].
  apply typed_in_u_minus_sound, Ht.
Qed.

Open Scope nterm_scope.

Lemma csucc_typed : forall G, system_u_minus ;; G ⊢ church csucc ⇑ Pi nat' nat'.
Proof. intros G. exact (certificate G csucc (CNat ~> CNat) ltac:(vm_compute; reflexivity) resolve_csucc). Qed.

Lemma cpred_typed : forall G, system_u_minus ;; G ⊢ church cpred ⇑ Pi nat' nat'.
Proof. intros G. exact (certificate G cpred (CNat ~> CNat) ltac:(vm_compute; reflexivity) resolve_cpred). Qed.

Lemma is_zero_typed : forall G, system_u_minus ;; G ⊢ church is_zero ⇑ Pi nat' bool'.
Proof. intros G. exact (certificate G is_zero (CNat ~> CBool) ltac:(vm_compute; reflexivity) resolve_is_zero). Qed.

Lemma nat'_star : forall G, system_u_minus ;; G ⊢ nat' ⇑ Srt Star.
Proof. intros G. exact (certificate G CNat ⋆ ltac:(vm_compute; reflexivity) resolve_CNat). Qed.

Lemma looping0_typed_any : forall G, system_u_minus ;; G ⊢ looping 0 ⇑ looping_ty.
Proof.
  intros G. apply synth_closed; [exact looping0_typed | ].
  exact (resolve_closed_term L0 (looping 0) resolve_L0).
Qed.

Close Scope nterm_scope.

(** ** Translated types *)

Lemma resolve_tr_ty : forall A, resolve [] (tr_ty A) = Ok (tty A).
Proof.
  induction A as [|A IHA B IHB].
  - reflexivity.
  - unfold translated_type, build. cbn [tr_ty resolve].
    rewrite IHA. cbn [bind]. rewrite IHB. reflexivity.
Qed.

Lemma resolve_tr_ty_any : forall ns A, resolve ns (tr_ty A) = Ok (tty A).
Proof. intros ns A. exact (resolve_closed _ _ ns (resolve_tr_ty A)). Qed.

Lemma tty_closed : forall A, closed (tty A) = true.
Proof. intros A. exact (resolve_closed_term _ _ (resolve_tr_ty A)). Qed.

Lemma tty_nat : tty PCF.Ty.tnat = nat'.
Proof. reflexivity. Qed.

Lemma tty_arrow : forall A B, tty (PCF.Ty.tarr A B) = Pi (tty A) (tty B).
Proof.
  intros A B. pose proof (resolve_tr_ty (PCF.Ty.tarr A B)) as H.
  cbn [tr_ty resolve] in H. rewrite (resolve_tr_ty A) in H. cbn [bind] in H.
  rewrite (resolve_tr_ty B) in H. cbn [bind] in H.
  injection H as <-. unfold arrow. now rewrite lift_closed by apply tty_closed.
Qed.

(** Every translated type is a type of sort ∗. *)
Lemma tty_star : forall A G, system_u_minus ;; G ⊢ tty A ⇑ Srt Star.
Proof.
  induction A as [|A IHA B IHB]; intros G.
  - apply nat'_star.
  - rewrite tty_arrow. eapply S_Pi; [apply IHA | apply rt_refl | apply IHB | apply rt_refl | ].
    reflexivity.
Qed.

Lemma tty_chk_star : forall A G, system_u_minus ;; G ⊢ tty A ⇓ Srt Star.
Proof. intros A G. eapply C_Synth; [apply tty_star | apply conv_refl]. Qed.

(** ** Numerals, for every k *)

Definition iterv (k : nat) : term := Nat.iter k (App (Var 1)) (Var 0).

Lemma resolve_iter_f : forall k, resolve ["x"; "f"; "X"]%string (iter_f k) = Ok (iterv k).
Proof.
  induction k as [|k IH]; [reflexivity | ].
  cbn [iter_f]. unfold napp. cbn [resolve]. rewrite IH. reflexivity.
Qed.

Lemma resolve_numeral : forall k, resolve [] (numeral k) = Ok (Ann (Lam (Lam (Lam (iterv k)))) nat').
Proof.
  intros k. unfold numeral. cbn [resolve]. rewrite resolve_iter_f. reflexivity.
Qed.

Lemma church_numeral : forall k, church (numeral k) = Ann (Lam (Lam (Lam (iterv k)))) nat'.
Proof. intros k. unfold church, build. now rewrite resolve_numeral. Qed.

(** Under [X : ∗, f : X → X, x : X], [fᵏ x : X]. *)
Definition numeral_ctx : ctx := [Var 1; Pi (Var 0) (Var 1); Srt Star].

Lemma iterv_typed : forall k, system_u_minus ;; numeral_ctx ⊢ iterv k ⇑ Var 2.
Proof.
  induction k as [|k IH].
  - now apply S_Var.
  - change (Var 2) with (subst1 (Var 3) (iterv k)).
    eapply S_App; [now apply S_Var | apply rt_refl | eapply C_Synth; [exact IH | apply conv_refl]].
Qed.

Lemma numeral_typed : forall G k, system_u_minus ;; G ⊢ church (numeral k) ⇑ nat'.
Proof.
  intros G k. apply synth_closed.
  - rewrite church_numeral. eapply S_Ann; [apply nat'_star | apply rt_refl | ].
    rewrite nat'_form.
    eapply C_Lam; [apply rt_refl | ]. eapply C_Lam; [apply rt_refl | ].
    eapply C_Lam; [apply rt_refl | ].
    eapply C_Synth; [exact (iterv_typed k) | apply conv_refl].
  - exact (resolve_closed_term _ _ (resolve_closed _ _ [] (eq_trans (resolve_numeral k)
      (f_equal Ok (eq_sym (church_numeral k)))))).
Qed.

(** ** Application at closed types *)

Lemma synth_app_closed : forall G f u A B,
  system_u_minus ;; G ⊢ f ⇑ Pi A B -> system_u_minus ;; G ⊢ u ⇓ A -> closed B = true ->
  system_u_minus ;; G ⊢ App f u ⇑ B.
Proof.
  intros G f u A B Hf Hu Hc. rewrite <- (subst1_closed B u Hc).
  eapply S_App; [exact Hf | apply rt_refl | exact Hu].
Qed.


(** Substituting a closed type into the codomains of [Bool] and of the
    looping combinator's type. *)
Lemma subst1_bool_body : forall T, closed T = true ->
  subst1 (Pi (Var 0) (Pi (Var 1) (Var 2))) T = Pi T (Pi T T).
Proof.
  intros T H. unfold subst1. cbn. unfold lift.
  rewrite !(rename_closed_above T 0); first [reflexivity | exact H | intros; lia].
Qed.

Lemma subst1_looping_body : forall T, closed T = true ->
  subst1 (Pi (Pi (Var 0) (Var 1)) (Var 1)) T = Pi (Pi T T) T.
Proof.
  intros T H. unfold subst1. cbn. unfold lift.
  rewrite !(rename_closed_above T 0); first [reflexivity | exact H | intros; lia].
Qed.

(** [ifz T c a b = is_zero c T a b : T]. *)
Lemma ifz_typed : forall G A c a b,
  system_u_minus ;; G ⊢ c ⇓ nat' ->
  system_u_minus ;; G ⊢ a ⇓ tty A -> system_u_minus ;; G ⊢ b ⇓ tty A ->
  system_u_minus ;; G ⊢ App (App (App (App (church is_zero) c) (tty A)) a) b ⇑ tty A.
Proof.
  intros G A c a b Hc Ha Hb. pose proof (tty_closed A) as HT.
  assert (Hpi : closed (Pi (tty A) (tty A)) = true) by (apply closed_pi; assumption).
  apply (synth_app_closed _ _ _ (tty A)); [ | exact Hb | exact HT].
  apply (synth_app_closed _ _ _ (tty A)); [ | exact Ha | exact Hpi].
  rewrite <- (subst1_bool_body (tty A) HT).
  eapply S_App; [ | rewrite <- bool'_form; apply rt_refl | apply tty_chk_star].
  apply (synth_app_closed _ _ _ nat'); [apply is_zero_typed | exact Hc | ].
  exact (closed_church CBool eq_refl).
Qed.

(** [fix_A u = L₀ ⟦A⟧ u : ⟦A⟧]. *)
Lemma fix_typed : forall G A u,
  system_u_minus ;; G ⊢ u ⇓ Pi (tty A) (tty A) ->
  system_u_minus ;; G ⊢ App (App (looping 0) (tty A)) u ⇑ tty A.
Proof.
  intros G A u Hu. pose proof (tty_closed A) as HT.
  apply (synth_app_closed _ _ _ (Pi (tty A) (tty A))); [ | exact Hu | exact HT].
  rewrite <- (subst1_looping_body (tty A) HT).
  eapply S_App; [apply looping0_typed_any | rewrite <- looping_ty_form; apply rt_refl | ].
  apply tty_chk_star.
Qed.

(** ** Contexts and names *)

Definition tctx (G : pcf_ctx) : ctx := map (fun p => tty (snd p)) G.

Lemma resolve_tr_ctx : forall G, resolve_ctx (tr_ctx G) = Ok (map fst G, tctx G).
Proof.
  induction G as [|[x A] G IH]; [reflexivity | ].
  cbn [tr_ctx map resolve_ctx]. unfold tr_ctx in IH. rewrite IH. cbn [bind fst snd].
  rewrite resolve_tr_ty_any. reflexivity.
Qed.

(** PCF's [lookup] and the builder's [index_of] find the same entry. *)
Lemma lookup_bridge : forall G x A, PCF.Context.lookup G x = Some A ->
  exists n, index_of x (map fst G) = Some n /\ lookup (tctx G) n = Some (tty A).
Proof.
  intros G x A H. unfold lookup.
  enough (exists n, index_of x (map fst G) = Some n /\ nth_error (tctx G) n = Some (tty A))
    as (n & Hi & Hn) by (exists n; split; [exact Hi | rewrite Hn; cbn; now rewrite lift_closed by apply tty_closed]).
  induction G as [|[y B] G IH]; cbn in H |- *; [discriminate | ].
  destruct (String.eqb x y).
  - injection H as <-. now exists 0.
  - destruct (IH H) as (n & Hi & Hn). exists (S n). rewrite Hi. split; [reflexivity | exact Hn].
Qed.

Lemma tctx_bwf : forall G, bwf_ctx system_u_minus (tctx G).
Proof.
  induction G as [|[x A] G IH]; [constructor | ].
  cbn. econstructor; [exact IH | apply tty_star | apply rt_refl].
Qed.

(** ** Soundness of the translator *)

Lemma pbind_ok : forall X Y (r : pcf_result X) (f : X -> pcf_result Y) y,
  pbind r f = PCF.Checker.Ok y -> exists x, r = PCF.Checker.Ok x /\ f x = PCF.Checker.Ok y.
Proof. intros X Y [x|e] f y H; [now exists x | discriminate H]. Qed.

Lemma tr_check_eq : forall G t B, PCF.Checker.synthesizing t = true ->
  tr G t (Some B) =
  pbind (tr G t None) (fun p =>
    if PCF.Ty.ty_eqb (snd p) B then PCF.Checker.Ok (fst p, B)
    else PCF.Checker.Err (PCF.Checker.E_Mismatch t B (snd p))).
Proof. intros G t B H. destruct t; try discriminate H; reflexivity. Qed.

(** What a successful translation in each mode guarantees. *)
Definition tr_claim (G : pcf_ctx) (t : pcf_term) (e : option pcf_ty) : Prop :=
  forall u A u', tr G t e = PCF.Checker.Ok (u, A) -> resolve (map fst G) u = Ok u' ->
  match e with
  | None => system_u_minus ;; tctx G ⊢ u' ⇑ tty A
  | Some B => A = B /\ system_u_minus ;; tctx G ⊢ u' ⇓ tty B
  end.

Lemma check_claim_from_synth : forall t, PCF.Checker.synthesizing t = true ->
  (forall G, tr_claim G t None) -> forall G B, tr_claim G t (Some B).
Proof.
  intros t Hs Hsyn G B u A u' H Hr. rewrite tr_check_eq in H by exact Hs.
  apply pbind_ok in H as ([u0 A0] & H0 & H). cbn [fst snd] in H.
  destruct (PCF.Ty.ty_eqb A0 B) eqn:E; [ | discriminate H].
  injection H as <- <-. apply PCF.Ty.ty_eqb_eq in E. subst A0.
  split; [reflexivity | ]. eapply C_Synth; [exact (Hsyn G u0 B u' H0 Hr) | apply conv_refl].
Qed.

(** Splits every successful resolution of an application, annotation
    or λ in the context. *)
Ltac resolve_split_all :=
  repeat match goal with
  | H : resolve _ (napp _ _) = Ok _ |- _ => unfold napp in H
  | H : resolve _ (NApp _ _) = Ok _ |- _ =>
      cbn [resolve] in H; apply bind_ok in H as (? & ? & H);
      apply bind_ok in H as (? & ? & H); injection H as <-
  | H : resolve _ (NAnn _ _) = Ok _ |- _ =>
      cbn [resolve] in H; apply bind_ok in H as (? & ? & H);
      apply bind_ok in H as (? & ? & H); injection H as <-
  | H : resolve _ (NLam _ _) = Ok _ |- _ =>
      cbn [resolve] in H; apply bind_ok in H as (? & ? & H); injection H as <-
  | H : bind _ _ = Ok _ |- _ => apply bind_ok in H as (? & ? & H)
  | H : Ok _ = Ok _ |- _ => injection H as <-
  end.

(** Resolves the closed constants and translated types among them. *)
Ltac resolve_consts :=
  repeat match goal with
  | H : resolve _ csucc = Ok _ |- _ => rewrite (resolve_closed _ _ _ resolve_csucc) in H; injection H as <-
  | H : resolve _ cpred = Ok _ |- _ => rewrite (resolve_closed _ _ _ resolve_cpred) in H; injection H as <-
  | H : resolve _ is_zero = Ok _ |- _ => rewrite (resolve_closed _ _ _ resolve_is_zero) in H; injection H as <-
  | H : resolve _ L0 = Ok _ |- _ => rewrite (resolve_closed _ _ _ resolve_L0) in H; injection H as <-
  | H : resolve _ (tr_ty _) = Ok _ |- _ => rewrite resolve_tr_ty_any in H; injection H as <-
  end.

Theorem tr_sound : forall t G e, tr_claim G t e.
Proof.
  induction t as [x | x b IHb | f IHf a IHa | n | u IHu | u IHu | c IHc a IHa b IHb
                 | A u IHu | u IHu A]; intros G e.
  (* the check claims of synthesizing terms follow from their synth claims *)
  all: match goal with
       | |- tr_claim _ (PCF.Syntax.tlam _ _) _ => idtac
       | |- tr_claim _ (PCF.Syntax.tifz _ _ _) _ => idtac
       | |- tr_claim ?G ?t ?e =>
           destruct e as [B|];
           [ revert G B; apply check_claim_from_synth; [reflexivity | intros G] | ]
       end.
  (* variables *)
  1, 2: intros u A u' H Hr; cbn [tr] in H;
    destruct (PCF.Context.lookup G x) as [A0|] eqn:L; [ | discriminate H];
    injection H as <- <-; destruct (lookup_bridge G x A0 L) as (k & Hk & Hl);
    cbn [resolve] in Hr; rewrite Hk in Hr; injection Hr as <-; now apply S_Var.
  (* λ: only checks *)
  1: { destruct e as [B|]; intros u A u' H Hr; cbn [tr] in H; [ | discriminate H].
    destruct B as [|A0 C]; [discriminate H | ].
    apply pbind_ok in H as ([b0 C0] & H0 & H). injection H as <- <-.
    resolve_split_all.
    destruct (IHb ((x, A0) :: G) (Some C) b0 C0 _ H0 ltac:(eassumption)) as [-> Hb].
    split; [reflexivity | ]. rewrite tty_arrow. eapply C_Lam; [apply rt_refl | exact Hb]. }
  (* application *)
  1, 2: intros u A u' H Hr; cbn [tr] in H;
    apply pbind_ok in H as ([f0 F] & Hf & H); cbn [snd fst] in H;
    destruct F as [|A0 B0]; [discriminate H | ];
    apply pbind_ok in H as ([a0 A1] & Ha & H); injection H as <- <-;
    resolve_split_all;
    pose proof (IHf G None _ _ _ Hf ltac:(eassumption)) as Hsf;
    destruct (IHa G (Some A0) _ _ _ Ha ltac:(eassumption)) as [_ Hca];
    rewrite tty_arrow in Hsf; exact (synth_app_closed _ _ _ _ _ Hsf Hca (tty_closed B0)).
  (* literals *)
  1, 2: intros u A u' H Hr; cbn [tr] in H; injection H as <- <-;
    rewrite (resolve_closed _ _ _ (eq_trans (resolve_numeral n)
               (f_equal Ok (eq_sym (church_numeral n))))) in Hr;
    injection Hr as <-; apply numeral_typed.
  (* succ and pred *)
  1, 2, 3, 4: intros u' A u'' H Hr; cbn [tr] in H;
    apply pbind_ok in H as ([u0 A0] & Hu & H); injection H as <- <-; cbn [fst] in Hr;
    resolve_split_all; resolve_consts;
    destruct (IHu G (Some PCF.Ty.tnat) _ _ _ Hu ltac:(eassumption)) as [_ Hcu];
    first [ exact (synth_app_closed _ _ _ _ _ (csucc_typed _) Hcu (closed_church CNat eq_refl))
          | exact (synth_app_closed _ _ _ _ _ (cpred_typed _) Hcu (closed_church CNat eq_refl)) ].
  (* ifz: only checks *)
  1: { destruct e as [B|]; intros u A u' H Hr; cbn [tr] in H; [ | discriminate H].
    apply pbind_ok in H as ([c0 C0] & Hc0 & H).
    apply pbind_ok in H as ([a0 A0] & Ha0 & H).
    apply pbind_ok in H as ([b0 B0] & Hb0 & H). injection H as <- <-. cbn [fst] in Hr.
    unfold ifz in Hr. resolve_split_all. resolve_consts.
    destruct (IHc G (Some PCF.Ty.tnat) c0 C0 _ Hc0 ltac:(eassumption)) as [_ Hcc].
    destruct (IHa G (Some B) a0 A0 _ Ha0 ltac:(eassumption)) as [_ Hca].
    destruct (IHb G (Some B) b0 B0 _ Hb0 ltac:(eassumption)) as [_ Hcb].
    split; [reflexivity | ]. eapply C_Synth; [ | apply conv_refl].
    exact (ifz_typed _ _ _ _ _ Hcc Hca Hcb). }
  (* fix *)
  1, 2: intros u' A' u'' H Hr; cbn [tr] in H;
    apply pbind_ok in H as ([u0 A0] & Hu & H); injection H as <- <-; cbn [fst] in Hr;
    resolve_split_all; resolve_consts;
    destruct (IHu G (Some (PCF.Ty.tarr A A)) _ _ _ Hu ltac:(eassumption)) as [_ Hcu];
    rewrite tty_arrow in Hcu; exact (fix_typed _ _ _ Hcu).
  (* annotation *)
  1, 2: intros u' A' u'' H Hr; cbn [tr] in H;
    apply pbind_ok in H as ([u0 A0] & Hu & H); injection H as <- <-; cbn [fst] in Hr;
    resolve_split_all; resolve_consts;
    destruct (IHu G (Some A) _ _ _ Hu ltac:(eassumption)) as [_ Hcu];
    eapply S_Ann; [apply tty_star | apply rt_refl | exact Hcu].
Qed.

(** Everything the translator outputs is typed: the translated context is
    well formed, the translated type admissible, and the term checks. *)
Theorem translate_sound : forall G t A G' u,
  translate G t A = Ok (G', u) ->
  G' = tctx G /\ bwf_ctx system_u_minus G' /\ btype system_u_minus G' (tty A) /\
  system_u_minus ;; G' ⊢ u ⇓ tty A.
Proof.
  intros G t A G' u H. unfold translate in H.
  destruct (tr G t (Some A)) as [[u0 A0]|e] eqn:E; [ | discriminate H].
  rewrite resolve_tr_ctx in H.
  destruct (resolve (map fst G) u0) as [u1|x] eqn:R; [ | discriminate H].
  injection H as <- <-.
  destruct (tr_sound t G (Some A) u0 A0 u1 E R) as [_ Hc].
  split; [reflexivity | split; [apply tctx_bwf | split; [ | exact Hc]]].
  right. exists (Srt Star), Star. split; [apply tty_star | apply rt_refl].
Qed.

(** ** Completeness: PCF-typed programs are translated *)

Lemma tr_synthesizing : forall G t u A, tr G t None = PCF.Checker.Ok (u, A) ->
  PCF.Checker.synthesizing t = true.
Proof. intros G t u A H. destruct t; try discriminate H; reflexivity. Qed.

Theorem tr_complete : forall G t A,
  PCF.Checker.chk G t A -> exists u, tr G t (Some A) = PCF.Checker.Ok (u, A).
Proof.
  intros G t A H.
  enough (Hb : (forall G t A, PCF.Checker.synth G t A ->
                  exists u, tr G t None = PCF.Checker.Ok (u, A)) /\
               (forall G t A, PCF.Checker.chk G t A ->
                  exists u, tr G t (Some A) = PCF.Checker.Ok (u, A)))
    by exact (proj2 Hb G t A H).
  clear G t A H.
  apply PCF.Checker.bidir_ind; intros; cbn [tr];
    repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end.
  all: repeat match goal with H : tr _ _ _ = PCF.Checker.Ok _ |- context [tr ?G ?t ?e] =>
         match type of H with tr G t e = _ => rewrite H; cbn [pbind fst snd] end end.
  all: try (eexists; reflexivity).
  - match goal with H : PCF.Context.lookup _ _ = Some _ |- _ => rewrite H end. eexists; reflexivity.
  - (* switch: a synthesizing term checks against its type *)
    match goal with H : tr ?G ?t None = PCF.Checker.Ok _ |- _ =>
      rewrite (tr_check_eq G t _ (tr_synthesizing _ _ _ _ H)), H end.
    cbn [pbind fst snd]. rewrite PCF.Ty.ty_eqb_refl. eexists; reflexivity.
Qed.

(** The translation of a PCF-typed program always resolves: its variables
    are bound in PCF, and the encodings are closed. *)
Definition resolves_claim (G : pcf_ctx) (t : pcf_term) (e : option pcf_ty) : Prop :=
  forall u A, tr G t e = PCF.Checker.Ok (u, A) -> exists u', resolve (map fst G) u = Ok u'.

Lemma resolves_check_from_synth : forall t, PCF.Checker.synthesizing t = true ->
  (forall G, resolves_claim G t None) -> forall G B, resolves_claim G t (Some B).
Proof.
  intros t Hs Hsyn G B u A H. rewrite tr_check_eq in H by exact Hs.
  apply pbind_ok in H as ([u0 A0] & H0 & H). cbn [fst snd] in H.
  destruct (PCF.Ty.ty_eqb A0 B); [ | discriminate H].
  injection H as <- <-. exact (Hsyn G u0 A0 H0).
Qed.

(** Rewrites the resolutions of the parts and closes the goal. *)
Ltac resolve_parts :=
  unfold ifz, napp; cbn [resolve];
  repeat match goal with H : resolve _ ?x = Ok _ |- context [resolve _ ?x] => rewrite H; cbn [bind] end;
  rewrite ?(resolve_closed _ _ _ resolve_csucc), ?(resolve_closed _ _ _ resolve_cpred),
          ?(resolve_closed _ _ _ resolve_is_zero), ?(resolve_closed _ _ _ resolve_L0),
          ?resolve_tr_ty_any; cbn [bind];
  repeat match goal with H : resolve _ ?x = Ok _ |- context [resolve _ ?x] => rewrite H; cbn [bind] end;
  eexists; reflexivity.

Theorem tr_resolves : forall t G e, resolves_claim G t e.
Proof.
  induction t as [x | x b IHb | f IHf a IHa | n | u IHu | u IHu | c IHc a IHa b IHb
                 | A u IHu | u IHu A]; intros G e.
  all: match goal with
       | |- resolves_claim _ (PCF.Syntax.tlam _ _) _ => idtac
       | |- resolves_claim _ (PCF.Syntax.tifz _ _ _) _ => idtac
       | |- resolves_claim ?G ?t ?e =>
           destruct e as [B|];
           [ revert G B; apply resolves_check_from_synth; [reflexivity | intros G] | ]
       end.
  all: intros u0 A0 H; cbn [tr] in H.
  (* variables *)
  1, 2: destruct (PCF.Context.lookup G x) as [A1|] eqn:L; [ | discriminate H];
    injection H as <- <-; destruct (lookup_bridge G x A1 L) as (k & Hk & _);
    cbn [resolve]; rewrite Hk; eexists; reflexivity.
  (* λ *)
  1: { destruct e as [B|]; [ | discriminate H]. destruct B as [|A1 C]; [discriminate H | ].
       apply pbind_ok in H as ([b0 C0] & H0 & H). injection H as <- <-.
       destruct (IHb ((x, A1) :: G) (Some C) b0 C0 H0) as [b1 Hb1].
       cbn [resolve]. cbn [map fst] in Hb1. rewrite Hb1. eexists; reflexivity. }
  (* application *)
  1, 2: apply pbind_ok in H as ([f0 F] & Hf & H); cbn [snd fst] in H;
    destruct F as [|A1 B1]; [discriminate H | ];
    apply pbind_ok in H as ([a0 A2] & Ha & H); injection H as <- <-;
    destruct (IHf G None f0 _ Hf) as [f1 Hf1];
    destruct (IHa G (Some A1) a0 A2 Ha) as [a1 Ha1];
    resolve_parts.
  (* literals *)
  1, 2: injection H as <- <-;
    rewrite (resolve_closed _ _ _ (eq_trans (resolve_numeral n)
               (f_equal Ok (eq_sym (church_numeral n))))); eexists; reflexivity.
  (* succ, pred *)
  1, 2, 3, 4: apply pbind_ok in H as ([u1 A1] & Hu & H); injection H as <- <-; cbn [fst];
    destruct (IHu G (Some PCF.Ty.tnat) u1 A1 Hu) as [u2 Hu2]; resolve_parts.
  (* ifz *)
  1: { destruct e as [B|]; [ | discriminate H].
       apply pbind_ok in H as ([c0 C0] & Hc0 & H).
       apply pbind_ok in H as ([a0 A1] & Ha0 & H).
       apply pbind_ok in H as ([b0 B0] & Hb0 & H). injection H as <- <-. cbn [fst].
       destruct (IHc G (Some PCF.Ty.tnat) c0 C0 Hc0) as [c1 Hc1].
       destruct (IHa G (Some B) a0 A1 Ha0) as [a1 Ha1].
       destruct (IHb G (Some B) b0 B0 Hb0) as [b1 Hb1].
       resolve_parts. }
  (* fix *)
  1, 2: apply pbind_ok in H as ([u1 A1] & Hu & H); injection H as <- <-; cbn [fst];
    destruct (IHu G (Some (PCF.Ty.tarr A A)) u1 A1 Hu) as [u2 Hu2]; resolve_parts.
  (* annotation *)
  1, 2: apply pbind_ok in H as ([u1 A1] & Hu & H); injection H as <- <-; cbn [fst];
    destruct (IHu G (Some A) u1 A1 Hu) as [u2 Hu2]; resolve_parts.
Qed.

(** ** Type preservation *)

(** PCF ⊢ t ⇓ A, in the bidirectional system of strictness-pcf, gives a
    translation that checks against ⟦A⟧ in ⟦Γ⟧. *)
Theorem translation_preserves_typing : forall G t A,
  PCF.Checker.chk G t A ->
  exists u, translate G t A = Ok (tctx G, u) /\ system_u_minus ;; tctx G ⊢ u ⇓ tty A.
Proof.
  intros G t A H. destruct (tr_complete G t A H) as [u0 E].
  destruct (tr_resolves t G (Some A) u0 A E) as [u R].
  assert (T : translate G t A = Ok (tctx G, u)).
  { unfold translate. rewrite E, resolve_tr_ctx. cbn [bind]. rewrite R. reflexivity. }
  exists u. split; [exact T | ].
  destruct (translate_sound G t A _ _ T) as (_ & _ & _ & Hc). exact Hc.
Qed.

(** The same from a run of the PCF checker. *)
Corollary checked_translation_typed : forall G t A,
  PCF.Checker.check G t A = PCF.Checker.Ok tt ->
  exists u, translate G t A = Ok (tctx G, u) /\ system_u_minus ;; tctx G ⊢ u ⇓ tty A.
Proof. intros G t A H. apply translation_preserves_typing, PCF.Checker.check_sound, H. Qed.
