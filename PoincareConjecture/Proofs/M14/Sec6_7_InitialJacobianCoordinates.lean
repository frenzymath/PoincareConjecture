import PoincareConjecture.Proofs.M14.Sec6_3_InitialJacobiDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 τ x y}
  (R : M14SquareRootPath G p)

private theorem eq_zero_of_heq_zero {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} (hv : HEq (0 : G.Horizontal r) v) : v = 0 := by
  cases h
  exact (eq_of_heq hv).symm

theorem tendsto_initialGauge_scaledField
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (b : G.gaugeCover.index)
    (F : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    {d : ℝ} (hd : 0 < d) (hsub : Icc 0 d ⊆ M14SqrtParameterInterval 0 τ)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc 0 d))
    (hrec : ∀ r ∈ Icc 0 d, (G.gaugeCover.cylinder b).toSpacetime (β r) = R.curve r)
    (hclock : ∀ r ∈ Icc 0 d, (β r).1.val = T - r ^ 2)
    (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval 0 τ))
    (hzero : Q.field 0 = 0) (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ ∞ f (Icc 0 d))
    (hfield : ∀ r ∈ Icc 0 d, HEq (Q.field r)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (f r))) :
    ∃ v : EuclideanSpace ℝ (Fin n),
      HEq (M14JacobiFirstDerivative Q 0)
        ((G.gaugeCover.metric b).spatialTangentEquiv (β 0).1 (β 0).2 v) ∧
      Tendsto (fun r : ℝ => r⁻¹ • f r) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hfield0 := hfield 0 h0
  rw [hzero] at hfield0
  have hf0 : f 0 = 0 := by
    apply ((G.gaugeCover.metric b).spatialTangentEquiv (β 0).1 (β 0).2).injective
    rw [map_zero]
    exact eq_zero_of_heq_zero (hrec 0 h0) hfield0
  have hR := R.smooth.mono R.interval_subset
  have hrestrict := horizontalCovariantDerivative_restrict_subset Q.extension hsub
    (uniqueDiffOn_Icc hd 0 h0) ((hR 0 (hsub h0)).mdifferentiableWithinAt (by simp))
  have hderiv := (heq_of_eq hrestrict).trans
    (horizontalCovariantDerivative_lifted_gauge b hCoordinates F T (β 0).2
      hβ hrec hclock (pullbackExtensionRestrict Q.extension hsub) f hfield h0
      (uniqueDiffOn_Icc hd 0 h0))
  rw [hf0, map_zero, add_zero] at hderiv
  refine ⟨derivWithin f (Icc 0 d) 0, hderiv, ?_⟩
  have h := hasDerivWithinAt_iff_tendsto_slope.mp
    ((hf 0 h0).differentiableWithinAt (by simp)).hasDerivWithinAt
  rw [Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hd] at h
  change Tendsto (fun r : ℝ => slope f 0 r) (𝓝[>] (0 : ℝ))
    (𝓝 (derivWithin f (Icc 0 d) 0)) at h
  simpa only [slope_def_module, hf0, sub_zero] using h

end PoincareConjecture.M14
