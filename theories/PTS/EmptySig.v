(** * The empty signature

    The developments of lecture 6 declare no constants: their reductions,
    conversions and judgments are those of the empty signature [∅].  This
    module gives them the notations that the kernel's sections use for
    their own signature, with [∅] in its place.  The kernel modules do not
    import it, and neither should a development with declarations. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Syntax Signature Reduction NormalOrder Typing Bidir.

Notation "t ⇝ u" := (red1 ∅ t u).
Notation "t ⇝* u" := (red ∅ t u).
Notation "t ≡ u" := (conv ∅ t u).
Notation "t ⇝ₙ u" := (nstep ∅ t u).
Notation "t ⇝ₙ* u" := (clos_refl_trans term (nstep ∅) t u).
Notation "S ;; G ⊢ t ∈ A" := (has_type S ∅ G t A).
Notation "S ;; G ⊢ t ⇑ A" := (synth S ∅ G t A).
Notation "S ;; G ⊢ t ⇓ A" := (chk S ∅ G t A).
