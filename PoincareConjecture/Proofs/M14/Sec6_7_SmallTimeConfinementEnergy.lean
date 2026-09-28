import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeConfinementGauge
import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyDisplacement










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)




theorem squarePath_gauge_prefix_displacement_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {U K : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hKU : K ⊆ U) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcoercive : ∀ q ∈ K, ∀ v : EuclideanSpace ℝ (Fin n),
      κ * ‖v‖ ^ 2 ≤ ((G.gaugeCover.metric b).metric (lift q).1.val).inner (lift q).2 v v)
    {a c : ℝ} (hac : a < c) (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ K) :
    κ * ‖(lift (p.curve (c ^ 2))).2.val - (lift (p.curve (a ^ 2))).2.val‖ ^ 2 ≤
      (Real.sqrt τ₂ - Real.sqrt τ₁) *
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s := by
  let v := fun s => (lift (p.curve (s ^ 2))).2.val
  have hsrcU : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U := fun s hs => hKU (hsrc s hs)
  obtain ⟨hv, hvd, hvLp⟩ :=
    squarePath_gauge_derivative_memLp p b lift hM12 hlift hright hac hAa hcB hsrcU
  have hder : IntervalIntegrable (fun s => ‖deriv v s‖ ^ 2) volume a c :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hac.le).mpr
      ((memLp_two_iff_integrable_sq_norm hvLp.aestronglyMeasurable).mp hvLp)
  have hk : IntervalIntegrable (pathSquareKinetic p) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := squarePath_kinetic_intervalIntegrable p hM12
  have hkp : IntervalIntegrable (pathSquareKinetic p) volume a c := by
    apply hk.mono_set
    simpa only [uIcc_of_le hac.le, uIcc_of_le (Real.sqrt_le_sqrt p.tau_lt.le)] using
      Icc_subset_Icc hAa hcB
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hac.le (hder.const_mul κ) hkp
    (fun s hs => (hcoercive _ (hsrc s (Ioo_subset_Icc_self hs)) (deriv v s)).trans_eq
      (squarePath_gauge_prefix_kinetic_eq b lift p hlift hright hAa hcB hsrcU hs))
  rw [intervalIntegral.integral_const_mul] at hi
  have hn (s : ℝ) : 0 ≤ pathSquareKinetic p s :=
    (G.spacetime.horizontalMetric.toRiemannianMetric.toCore (p.curve (s ^ 2))).re_inner_nonneg _
  have hwhole := intervalIntegral.integral_mono_interval hAa hac.le hcB
    (ae_of_all _ hn) hk
  have hwhole0 : 0 ≤ ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s :=
    intervalIntegral.integral_nonneg (Real.sqrt_le_sqrt p.tau_lt.le) (fun s _ => hn s)
  have hdisp := norm_sub_sq_le_interval_energy hac.le hv
    (fun s hs => (hvd s hs).differentiableAt.differentiableWithinAt) hvLp
  calc
    κ * ‖v c - v a‖ ^ 2 ≤ κ * ((c - a) * ∫ s in a..c, ‖deriv v s‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hdisp hκ
    _ = (c - a) * (κ * ∫ s in a..c, ‖deriv v s‖ ^ 2) := by ring
    _ ≤ (c - a) * ∫ s in a..c, pathSquareKinetic p s :=
      mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hac.le)
    _ ≤ (c - a) * ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s :=
      mul_le_mul_of_nonneg_left hwhole (sub_nonneg.mpr hac.le)
    _ ≤ (Real.sqrt τ₂ - Real.sqrt τ₁) *
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pathSquareKinetic p s :=
      mul_le_mul_of_nonneg_right (sub_le_sub hcB hAa) hwhole0

end PoincareConjecture.M14
