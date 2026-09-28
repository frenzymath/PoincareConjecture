import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.JetBounds
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Operations












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem isInvertible_of_uniformEllipticity
    {A : E →L[ℝ] E →L[ℝ] ℝ} {a : ℝ} (ha : 0 < a)
    (hA : ∀ v, a * ‖v‖ ^ 2 ≤ A v v) : A.IsInvertible := by
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hzero : A v v = 0 := by simp [hv]
    have hnorm : ‖v‖ = 0 := by
      by_contra hne
      have hn : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hne)
      have hp : 0 < a * ‖v‖ ^ 2 := mul_pos ha (sq_pos_of_pos hn)
      exact (not_lt_of_ge (hA v)) (by simpa [hzero] using hp)
    exact norm_eq_zero.mp hnorm
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩


theorem isCompact_bounded_uniformlyElliptic (a C : ℝ) :
    IsCompact {A : E →L[ℝ] E →L[ℝ] ℝ | ‖A‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ A v v} := by
  let : ProperSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    FiniteDimensional.proper ℝ (E →L[ℝ] E →L[ℝ] ℝ)
  apply (Metric.isCompact_iff_isClosed_bounded (α := E →L[ℝ] E →L[ℝ] ℝ)).mpr
  constructor
  · have hn : IsClosed {A : E →L[ℝ] E →L[ℝ] ℝ | ‖A‖ ≤ C} :=
      isClosed_le (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)) continuous_const
    apply hn.inter
    change IsClosed {A : E →L[ℝ] E →L[ℝ] ℝ | ∀ v, a * ‖v‖ ^ 2 ≤ A v v}
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous)
  · exact isBounded_iff_forall_norm_le.mpr ⟨C, fun _ hA => hA.1⟩


theorem hasUniformJetBoundsOn_inverse_elliptic
    {a : ℝ} (ha : 0 < a) (C : ℝ) (n : ℕ) :
    HasUniformJetBoundsOn n
      {A : E →L[ℝ] E →L[ℝ] ℝ | ‖A‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ A v v}
      (fun _ : Unit => ContinuousLinearMap.inverse) := by
  intro m _hm
  have hcont : ContinuousOn
      (iteratedFDeriv ℝ m (ContinuousLinearMap.inverse :
        (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)))
      {A : E →L[ℝ] E →L[ℝ] ℝ | ‖A‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ A v v} := by
    intro A hA
    exact ((isInvertible_of_uniformEllipticity ha hA.2).contDiffAt_map_inverse
      (n := m)).continuousAt_iteratedFDeriv le_rfl |>.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_bounded_uniformlyElliptic (E := E) a C).exists_bound_of_continuousOn hcont
  exact ⟨B, fun _ A hA => hB A hA⟩


theorem contDiffOn_inverse_metric {ι : Type*} {U : Set E}
    (hU : IsOpen U) {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) (i : ι) :
    ContDiffOn ℝ ∞ (fun x => (A i x).inverse) U := by
  intro x hx
  exact ((isInvertible_of_uniformEllipticity ha (hell i x hx)).contDiffAt_map_inverse.comp x
    ((hA i).contDiffAt (hU.mem_nhds hx))).contDiffWithinAt


theorem hasUniformJetBoundsOn_inverse_metric {ι : Type*} {U : Set E}
    (hU : IsOpen U) {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hjets : ∀ n, HasUniformJetBoundsOn n U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) (n : ℕ) :
    HasUniformJetBoundsOn n U (fun i x => (A i x).inverse) := by
  obtain ⟨C, hC⟩ := hjets 0 0 le_rfl
  let K := {B : E →L[ℝ] E →L[ℝ] ℝ | ‖B‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v}
  let T := {B : E →L[ℝ] E →L[ℝ] ℝ | B.IsInvertible}
  have hT : IsOpen T := ContinuousLinearEquiv.isOpen
  have hK : K ⊆ T := fun B hB => isInvertible_of_uniformEllipticity ha hB.2
  have houter : HasUniformJetBoundsOn n K (fun _ : Unit => ContinuousLinearMap.inverse) := by
    intro m hm
    obtain ⟨B, hB⟩ := hasUniformJetBoundsOn_inverse_elliptic (E := E) ha C n m hm
    exact ⟨B, fun _ x hx => hB () x hx⟩
  apply HasUniformJetBoundsOn.comp_fixed_on hU hT (hjets n) houter
    (fun i => (hA i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    (fun B hB => hB.contDiffAt_map_inverse.contDiffWithinAt) ?_ hK
  intro i x hx
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hC i x hx, hell i x hx⟩

end PoincareConjecture.CoordinateTransition
