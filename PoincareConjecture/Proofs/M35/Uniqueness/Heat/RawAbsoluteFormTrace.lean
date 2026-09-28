import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawFormRecovery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

private theorem hasDerivAt_shifted_curve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : ℝ → E} {a t : ℝ} (hw : DifferentiableAt ℝ w (t - a)) :
    HasDerivAt (fun s => w (s - a)) (deriv w (t - a)) t := by
  have hsd : HasDerivAt (fun s : ℝ => s - a) 1 t := (hasDerivAt_id t).sub_const a
  simpa only [Function.comp_def, one_smul] using hw.hasDerivAt.scomp t hsd

private theorem shift_form_trace {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : E →L[ℝ] H) (L : ℝ → E → H) (Q : ℝ → E → E → ℝ)
    {a b : ℝ} (w : ℝ → E) (U : ℝ → H)
    (hw : ∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t)
    (hg : ∀ t ∈ Ioo 0 (b - a), I (w t) = U t)
    (hd : ∀ t ∈ Ioo 0 (b - a), I (deriv w t) = deriv U t)
    (he : ∀ t ∈ Ioo 0 (b - a), ∀ z,
      inner ℝ (I z) (deriv U t) = inner ℝ (I z) (L (a + t) (w t)) - Q (a + t) z (w t)) :
    ∃ W : ℝ → E, (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t) ∧
      (∀ t ∈ Ioo a b, I (W t) = U (t - a)) ∧
      (∀ t ∈ Ioo a b, ∀ z,
        inner ℝ (I z) (I (deriv W t)) = inner ℝ (I z) (L t (W t)) - Q t z (W t)) := by
  have hs {t : ℝ} (ht : t ∈ Ioo a b) : t - a ∈ Ioo 0 (b - a) := by
    constructor <;> linarith only [ht.1, ht.2]
  let W := fun t => w (t - a)
  refine ⟨W, fun t ht => (hw (t - a) (hs ht)).comp t
    (contDiffAt_id.sub contDiffAt_const), fun t ht => hg (t - a) (hs ht), ?_⟩
  intro t ht z
  have hdw : deriv W t = deriv w (t - a) :=
    (hasDerivAt_shifted_curve ((hw (t - a) (hs ht)).differentiableAt (by simp))).deriv
  rw [hdw, hd (t - a) (hs ht)]
  simpa only [show a + (t - a) = t by ring, W] using he (t - a) (hs ht) z

theorem exists_raw_compact_absolute_form_trace {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set X} (hK : IsCompact K) (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U) :
    ∃ W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t) ∧
      (∀ t ∈ Ioo a b, finiteHilbertMap (dirichletInclusion K) (W t) = U (t - a)) ∧
      (∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
          (finiteHilbertMap (dirichletInclusion K) (deriv W t)) =
            inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
              (rawLowerFormOperator (F.connection t) hK.isClosed η hη (W t)) -
                principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη)
                  z (W t)) := by
  have hrec : ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 (b - a)), w t = v t) ∧
      (∀ t ∈ Ioo 0 (b - a), finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      (∀ t ∈ Ioo 0 (b - a),
        finiteHilbertMap (dirichletInclusion K) (deriv w t) = deriv U t) ∧
      (∀ t ∈ Ioo 0 (b - a), ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (w t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη)
                z (w t)) :=
    exists_raw_compact_vector_heat_smooth_form F hab hJ hK η hη hηK hsol
  obtain ⟨w, hw, _, hgraph, hd, heq⟩ := hrec
  exact shift_form_trace (finiteHilbertMap (dirichletInclusion K))
    (fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη)
    (fun t => principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη))
    w U hw hgraph hd heq

end PoincareConjecture.M35.Uniqueness.Heat
