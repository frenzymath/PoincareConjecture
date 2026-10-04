import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Lipschitz.LocalLipschitzMetric
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.MovingMetric
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootVelocityExtension

/-!
# Auxiliary spacetime distance and actual terminal tails

The Riemannian extended distance of the actual auxiliary metric induces
the given topology without completeness. An actual square path has
auxiliary speed squared `|A|^2 + 4*s^2`, so a uniform energy bound controls
every short terminal tail. Morgan-Tian Proposition 6.56 and Lemma 6.60,
pp. 133, 135-136.
-/

set_option autoImplicit false
-- The metric installs fiber norms without changing the tangent topology.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- The intrinsic extended distance of `g + dt^2`, Proposition 6.56,
p. 133. It is defined on the unchanged actual spacetime. -/
noncomputable def auxiliarySpacetimeEDist (F : GeneralizedFlowSpacetime n X time I)
    (q z : F.Point) : ℝ≥0∞ :=
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  riemannianEDist (spacetimeModel n) q z

/-- The auxiliary extended distance vanishes at the diagonal,
Proposition 6.56, p. 133. -/
theorem auxiliarySpacetimeEDist_self (F : GeneralizedFlowSpacetime n X time I)
    (q : F.Point) : auxiliarySpacetimeEDist F q q = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  exact riemannianEDist_self

/-- Symmetry of the actual auxiliary extended distance,
Proposition 6.56, p. 133. -/
theorem auxiliarySpacetimeEDist_comm (F : GeneralizedFlowSpacetime n X time I)
    (q z : F.Point) : auxiliarySpacetimeEDist F q z = auxiliarySpacetimeEDist F z q := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  exact riemannianEDist_comm

/-- The actual auxiliary extended distance satisfies the triangle
inequality, Proposition 6.56, p. 133. -/
theorem auxiliarySpacetimeEDist_triangle (F : GeneralizedFlowSpacetime n X time I)
    (q z w : F.Point) : auxiliarySpacetimeEDist F q w ≤
      auxiliarySpacetimeEDist F q z + auxiliarySpacetimeEDist F z w := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  exact riemannianEDist_triangle

/-- The auxiliary distance is continuous for the original spacetime
topology, including physical endpoints, Proposition 6.56, p. 133. -/
theorem auxiliarySpacetimeEDist_continuous (F : GeneralizedFlowSpacetime n X time I)
    (q : F.Point) : Continuous (auxiliarySpacetimeEDist F q) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  let : EMetricSpace F.Point := .ofRiemannianMetric (spacetimeModel n) F.Point
  exact continuous_const.edist continuous_id

/-- Every actual neighborhood contains a positive auxiliary distance
ball. No global completeness or connectedness is needed, Proposition
6.56, p. 133. -/
theorem auxiliarySpacetimeEDist_ball_subset (F : GeneralizedFlowSpacetime n X time I)
    {q : F.Point} {U : Set F.Point} (hU : U ∈ 𝓝 q) :
    ∃ ε : ℝ, 0 < ε ∧ {z | auxiliarySpacetimeEDist F q z < ENNReal.ofReal ε} ⊆ U := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  obtain ⟨ε, hε, hsub⟩ := setOfPred_riemannianEDist_lt_subset_nhds
    (spacetimeModel n) hU
  refine ⟨ε, hε, ?_⟩
  simpa only [auxiliarySpacetimeEDist, ENNReal.ofReal_coe_nnreal] using hsub

/-- A bound on actual auxiliary speed controls distance along a smooth
closed path segment, as used in Proposition 6.59, pp. 134-137. -/
theorem auxiliarySpacetimeEDist_le_of_velocity_bound
    (F : GeneralizedFlowSpacetime n X time I) {γ : ℝ → F.Point} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel n) 1 γ (Icc a b))
    (hv : ∀ s ∈ Ioo a b, auxiliarySpacetimeForm F (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1) ≤ C ^ 2) :
    auxiliarySpacetimeEDist F (γ a) (γ b) ≤ ENNReal.ofReal (C * (b - a)) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  apply (riemannianEDist_le_pathELength hγ rfl rfl hab).trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ _ in Ioo a b, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have h := hv s hs
      have heq : auxiliarySpacetimeForm F (γ s)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1) =
          ‖mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1‖ ^ 2 :=
        real_inner_self_eq_norm_sq (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)
      rw [heq] at h
      nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) γ s 1)]
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.ofReal_mul hC]

variable {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

/-- The actual square velocity has auxiliary squared norm
`|A|^2 + 4*s^2` on the full closed interval, Lemma 6.60, pp. 135-136. -/
theorem auxiliarySpacetimeForm_squareRoot_velocity (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval a b) :
    auxiliarySpacetimeForm G.spacetime (R.curve s)
      (mfderivWithin 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval a b) s 1)
      (mfderivWithin 𝓘(ℝ, ℝ) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval a b) s 1) =
      G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) + 4 * s ^ 2 := by
  rw [auxiliarySpacetimeForm_apply, ← squareRoot_horizontalVelocity_eq_projection R hs,
    squareRoot_velocity_clock R hs]
  ring

/-- An actual square-path energy bound controls every closed subsegment
in the auxiliary spacetime distance, Proposition 6.59, pp. 134-137. -/
theorem auxiliarySpacetimeEDist_squareRoot_le (R : M14SquareRootPath G p)
    {r t C : ℝ} (hr : Real.sqrt a ≤ r) (ht : t ≤ Real.sqrt b)
    (hrt : r ≤ t) (hC : 0 ≤ C)
    (henergy : ∀ s ∈ Ioo r t, G.spacetime.horizontalMetric.inner (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s) + 4 * s ^ 2 ≤ C ^ 2) :
    auxiliarySpacetimeEDist G.spacetime (R.curve r) (R.curve t) ≤
      ENNReal.ofReal (C * (t - r)) := by
  have hsub : Icc r t ⊆ M14SqrtParameterInterval a b :=
    fun _ hs => ⟨hr.trans hs.1, hs.2.trans ht⟩
  apply auxiliarySpacetimeEDist_le_of_velocity_bound G.spacetime hrt hC
    ((R.smooth.mono (hsub.trans R.interval_subset)).of_le (by simp))
  intro s hs
  have hfull : M14SqrtParameterInterval a b ∈ 𝓝 s :=
    Icc_mem_nhds (hr.trans_lt hs.1) (hs.2.trans_le ht)
  have hnorm := auxiliarySpacetimeForm_squareRoot_velocity R (hsub ⟨hs.1.le, hs.2.le⟩)
  rw [mfderivWithin_of_mem_nhds hfull] at hnorm
  exact hnorm.trans_le (henergy s hs)

end PoincareMT.M14
