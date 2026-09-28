import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.DisplacementFamily
import PoincareConjecture.Proofs.M14.Sec6_3_SquareFamilyAction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveEndpoints
import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T b c : ℝ} {gamma : ℝ → G.Point} {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j} {U : Set G.Point}

noncomputable def EndpointDisplacementFamily.cost
    (D : EndpointDisplacementFamily gamma T b c j lift U)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  ∫ s in 0..z.2, M14.squareCurveDensity G (fun r => D.family (r, z.1)) (Icc 0 b) s

theorem EndpointDisplacementFamily.cost_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (D : EndpointDisplacementFamily gamma T b c j lift U) (hb : 0 < b) :
    ContDiffOn ℝ ∞ D.cost (D.parameters ×ˢ Icc 0 b) := by
  exact M14.closedFamilyPrimitive_contDiffOn hb D.parameters_open _
    (M14.squareFamilyDensity_contDiffOn hM12 (uniqueDiffOn_Icc hb)
      D.parameters_open D.smooth)

theorem EndpointDisplacementFamily.exists_path
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (D : EndpointDisplacementFamily gamma T b c j lift U)
    {tau : ℝ} (htau : 0 < tau) (hs : Real.sqrt tau ≤ b)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.parameters)
    {x y : G.Point} (hx : gamma 0 = x) (hy : D.family (Real.sqrt tau, v) = y) :
    ∃ p : M14BackwardPath G T 0 tau x y,
      (∀ t ∈ Icc 0 tau, p.curve t = D.family (Real.sqrt t, v)) ∧
      M14BackwardLAction G p = D.cost (v, Real.sqrt tau) := by
  let alpha := fun s => D.family (s, v)
  have halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ alpha (Icc 0 b) :=
    D.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ hr => ⟨hr, hv⟩)
  have hsub : M14SqrtParameterInterval 0 tau ⊆ Icc 0 b := by
    intro r hr
    exact ⟨by simpa only [Real.sqrt_zero] using hr.1, hr.2.trans hs⟩
  have hclock (r : ℝ) (hr : r ∈ M14SqrtParameterInterval 0 tau) :
      G.spacetime.timeFunction (alpha r) = T - r ^ 2 := D.clock r (hsub hr) v hv
  have hstart : alpha (Real.sqrt 0) = x := by
    rw [Real.sqrt_zero]
    exact (D.initial v hv).trans hx
  let p := M14.backwardPathOfSquareCurveBetween hM12 (by norm_num : (0 : ℝ) ≤ 0)
    htau alpha (halpha.mono hsub) hclock hstart hy
  refine ⟨p, fun _ _ => rfl, ?_⟩
  have h := M14.integral_squareCurveDensity_eq_action_between hM12
    (by norm_num : (0 : ℝ) ≤ 0) htau alpha halpha hsub hclock hstart hy
  simpa only [p, EndpointDisplacementFamily.cost, alpha, Real.sqrt_zero] using h.symm

theorem EndpointDisplacementFamily.cost_zero
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (D : EndpointDisplacementFamily gamma T b c j lift U)
    {tau : ℝ} {x y : G.Point} (p : M14BackwardPath G T 0 tau x y)
    (hs : Real.sqrt tau ≤ b) (hx : gamma 0 = x)
    (htrace : EqOn p.curve (fun t => gamma (Real.sqrt t)) (Icc 0 tau)) :
    D.cost (0, Real.sqrt tau) = M14BackwardLAction G p := by
  have hy : D.family (Real.sqrt tau, 0) = y :=
    (D.recovery _ ⟨Real.sqrt_nonneg _, hs⟩).trans
      ((htrace ⟨p.tau_lt.le, le_rfl⟩).symm.trans p.curve_end)
  obtain ⟨r, hr, haction⟩ := D.exists_path hM12 p.tau_lt hs D.zero_mem hx hy
  apply haction.symm.trans
  apply M14.action_eq_of_curve_eqOn r p
  intro t ht
  rw [hr t (Ioo_subset_Icc_self ht)]
  exact (D.recovery _ ⟨Real.sqrt_nonneg _, (Real.sqrt_le_sqrt ht.2.le).trans hs⟩).trans
    (htrace (Ioo_subset_Icc_self ht)).symm

end PoincareConjecture.Proofs.M46
