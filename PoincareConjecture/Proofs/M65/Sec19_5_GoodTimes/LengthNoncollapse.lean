import PoincareConjecture.Proofs.M64.FamilyAdapters









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}



theorem m65FamilyLength_backward_lower_bound (C : M63FamilyConclusion G Gamma zeta)
    (E : M64AppliedFamilyEstimates G C) (circumference : ℝ) (h : 0 < circumference)
    (z : LoopTwoSphere) {s t ell : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hst : s ≤ t) (hell : ell ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) t) :
    ell * Real.exp (-G.K2 * (b - a)) ≤
      m62Length (G.product circumference h).flow ((C.solutions circumference h).curve z) s := by
  have hnonneg : 0 ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) s :=
    intervalIntegral.integral_nonneg_of_forall (by unfold curvePeriod; positivity)
      (fun _ => Real.sqrt_nonneg _)
  have hexp : Real.exp (G.K2 * (t - s)) ≤ Real.exp (G.K2 * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.1, ht.2])
      G.nonnegative.2.2)
  have hforward := (E.curve_estimates circumference h z).length_exponential s t hs ht hst
  have hscaled := mul_le_mul_of_nonneg_right
    (hell.trans (hforward.trans (mul_le_mul_of_nonneg_left hexp hnonneg)))
    (Real.exp_nonneg (-G.K2 * (b - a)))
  have hcancel : Real.exp (G.K2 * (b - a)) * Real.exp (-G.K2 * (b - a)) = 1 := by
    rw [← Real.exp_add]
    have hz : G.K2 * (b - a) + -G.K2 * (b - a) = 0 := by ring
    rw [hz, Real.exp_zero]
  simpa only [mul_assoc, hcancel, mul_one] using hscaled



theorem m65FamilyLength_short_or_earlier_lower_bound
    (C : M63FamilyConclusion G Gamma zeta) (E : M64AppliedFamilyEstimates G C)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere)
    {T ell : ℝ} (hT : T ∈ Icc a b) :
    (∀ t ∈ Icc T b, m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) t < ell) ∨
    (∀ s ∈ Icc a T, ell * Real.exp (-G.K2 * (b - a)) ≤
      m62Length (G.product circumference h).flow
        ((C.solutions circumference h).curve z) s) := by
  classical
  by_cases hshort : ∀ t ∈ Icc T b, m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) t < ell
  · exact Or.inl hshort
  · push Not at hshort
    obtain ⟨t, ht, hell⟩ := hshort
    refine Or.inr (fun s hs => m65FamilyLength_backward_lower_bound C E
      circumference h z ⟨hs.1, hs.2.trans hT.2⟩ ⟨hT.1.trans ht.1, ht.2⟩
        (hs.2.trans ht.1) hell)

end PoincareConjecture
