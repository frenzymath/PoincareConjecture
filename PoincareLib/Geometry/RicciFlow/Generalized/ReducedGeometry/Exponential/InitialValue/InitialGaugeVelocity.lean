import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialGaugePhase

/-!
# The exact initial coordinate velocity of every selected curve

Morgan-Tian Definition 6.17 and Claim 6.20, pp. 113-114. Actual
IVP coherence and the prescribed horizontal initial velocity give
the actual within coordinate velocity in a fixed initial gauge.
-/

set_option autoImplicit false
-- The fixed gauge spatial tangent is the Euclidean coordinate model.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- In a gauge with its prescribed initial lift, the actual selected
curve has coordinate initial velocity exactly twice the inverse gauge
tangent map applied to its initial vector, Claim 6.20, p. 114. -/
theorem initialValueCurve_gauge_initialVelocity
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    {T : ℝ} {Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))}
    {S d : ℝ} (hS : 0 < S) (hd : 0 < d) (hdS : d ≤ S)
    (hsurv : (Z, S) ∈ initialValueDomain G T ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc 0 d))
    (hrec : ∀ r ∈ Icc 0 d, (G.gaugeCover.cylinder b).toSpacetime (β r) =
      initialValueCurve G T ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) Z r)
    (hzero : β 0 = (t₀, x₀)) :
    derivWithin (fun r => (β r).2.val) (Icc 0 d) 0 =
      (2 : ℝ) • ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm Z := by
  obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hS).mp hsurv
  have hsub : Icc 0 d ⊆ M14SqrtParameterInterval 0 (S ^ 2) := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hS.le]
    exact Icc_subset_Icc le_rfl hdS
  have hrecP (r : ℝ) (hr : r ∈ Icc 0 d) :
      (G.gaugeCover.cylinder b).toSpacetime (β r) = P.square_path.curve r :=
    (hrec r hr).trans (initialValueCurve_eqOn_square hM04 hM12 P (hsub hr))
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hv := squareRootVelocity_gauge_subset b P.square_path hsub hβ hrecP h0
    (uniqueDiffOn_Icc hd 0 h0)
  rw [hzero] at hv
  obtain ⟨hstart, hinit⟩ := P.initial_velocity
  have hi : HEq (P.square_path.horizontal_velocity 0) ((2 : ℝ) • Z) :=
    (eqRec_heq hstart (P.square_path.horizontal_velocity 0)).symm.trans (heq_of_eq hinit)
  apply ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).injective
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact eq_of_heq (hv.symm.trans hi)

end PoincareMT.M14
