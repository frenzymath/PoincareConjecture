import PoincareConjecture.Proofs.M13.Geometry
import PoincareConjecture.Proofs.M13.TangentIsometry
import PoincareConjecture.Definitions.M13HorizontalTransport








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

noncomputable def normalizedHorizontalIsometry
    (P : ParabolicSpacetimeRescaling R Q hQ a) :
    ParabolicNormalizedHorizontalIsometry P := by
  have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  refine {
    linearEquiv := fun p ↦ ContinuousLinearEquiv.equivOfInverse
      ((1 / Real.sqrt Q : ℝ) • (P.horizontal p).toContinuousLinearMap)
      (Real.sqrt Q • (P.horizontal p).symm.toContinuousLinearMap)
      (by intro v; simp [smul_smul, hs])
      (by intro v; simp [smul_smul, hs])
    linearEquiv_eq := fun _ _ ↦ rfl
    inner_eq := ?_ }
  intro p v w
  change P.realization.spacetime.horizontalMetric.inner p
    ((1 / Real.sqrt Q : ℝ) • P.horizontal p v)
    ((1 / Real.sqrt Q : ℝ) • P.horizontal p w) =
      R.spacetime.horizontalMetric.inner p v w
  simp only [map_smul, smul_apply, smul_eq_mul, P.metric_eq, one_div]
  have hscale : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q = 1 := by
    rw [inv_sqrt_mul_inv_sqrt Q hQ.le, inv_mul_cancel₀ hQ.ne']
  calc
    _ = ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ * Q) *
        R.spacetime.horizontalMetric.inner p v w := by ring
    _ = _ := by rw [hscale, one_mul]

theorem parabolic_section_smooth_iff
    (V : HorizontalSection R.spacetime) (U : Set R.spacetime.Point) :
    IsSmoothHorizontalSectionOn (spacetimeRescaling R Q hQ a).realization.spacetime
      (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) V) U ↔
        IsSmoothHorizontalSectionOn R.spacetime V U := by
  let P := spacetimeRescaling R Q hQ a
  constructor
  · intro hV
    have h := P.horizontal_inverse_smooth.comp_contMDiffOn hV
    change IsSmoothHorizontalSectionOn R.spacetime
      (fun p ↦ (P.horizontal p).symm (P.horizontal p (V p))) U at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  · intro hV
    exact P.horizontal_smooth.comp_contMDiffOn hV

theorem parabolic_timeBracket
    (V : HorizontalSection R.spacetime) (p : R.spacetime.Point) :
    horizontalTimeBracket (spacetimeRescaling R Q hQ a).realization.spacetime
      (parabolicHorizontalSection (spacetimeRescaling R Q hQ a) V) p =
        (1 / Q : ℝ) • (spacetimeRescaling R Q hQ a).horizontal p
          (horizontalTimeBracket R.spacetime V p) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
      R.spacetime.Point := R.spacetime.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ R.spacetime.Point := R.spacetime.isManifold
  change (parabolicSpacetime R.spacetime Q hQ a).horizontalProjection p
    (VectorField.mlieBracket (spacetimeModel n)
      ((1 / Q : ℝ) • R.spacetime.timeVector)
      (horizontalSectionVectorField R.spacetime V) p) = _
  rw [VectorField.mlieBracket_const_smul_left
    (R.spacetime.timeVector_smooth.mdifferentiable (by simp) p), map_smul,
    parabolicSpacetime_projection]
  rfl

theorem horizontalMetric_inner_mdifferentiableAt
    (V W : HorizontalSection R.spacetime) (p : R.spacetime.Point)
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun q ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := R.spacetime.Horizontal) q (V q)) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun q ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := R.spacetime.Horizontal) q (W q)) p) :
    MDifferentiableAt (spacetimeModel n) 𝓘(ℝ)
      (fun q ↦ R.spacetime.horizontalMetric.inner q (V q) (W q)) p := by
  have htotal : MDifferentiableAt (spacetimeModel n) ((spacetimeModel n).prod 𝓘(ℝ))
      (fun q : R.spacetime.Point ↦ Bundle.TotalSpace.mk' ℝ
        (E := Bundle.Trivial R.spacetime.Point ℝ) q
        (R.spacetime.horizontalMetric.inner q (V q) (W q))) p := by
    apply MDifferentiableAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact R.spacetime.horizontalMetric.contMDiff.mdifferentiableAt (by simp)
    · exact hV
    · exact hW
  simp only [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2

end PoincareConjecture.M13
