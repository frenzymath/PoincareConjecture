import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Identity

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem secondVariationIndexDensity_intervalIntegrable {J : Set ℝ} {F : RicciFlow 2 M J}
    {T τ₁ τ₂ : ℝ}
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (hclock : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J))
    (htime : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂), T - r ^ 2 ∈ interior J)
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V)
    (heuler : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      ∀ W : TangentSpace (𝓡 2) (V.baseSquareCurve r),
        regularizedEulerResidual F T V.baseSquareCurve
          (sqrtParameterInterval τ₁ τ₂) D.velocity_extension r W = 0) :
    IntervalIntegrable (secondVariationIndexDensity V D) volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  let C := sqrtParameterInterval τ₁ τ₂
  let raw := fun s ↦ variationParameterDeriv C V.parameterDomain
    (variationParameterDeriv C V.parameterDomain (variationActionDensity V)) (s, 0)
  let B := variationAccelerationBoundaryPair V D
  let dB := derivWithin B C
  let idx := secondVariationIndexDensity V D
  have hab : a < b := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hab
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hraw : ContinuousOn raw C :=
    (variationParameterDeriv_contDiffOn hC isOpen_Ioo _
      (variationParameterDeriv_contDiffOn hC isOpen_Ioo _
        (variationActionDensity_contDiffOn hpotential V))).continuousOn.comp
          (continuousOn_id.prodMk continuousOn_const) (fun s hs ↦ ⟨hs, hzero⟩)
  have hB : ContDiffOn ℝ ∞ B C := variationAccelerationBoundaryPair_contDiffOn V D hclock
  have hdB : ContinuousOn dB C := (hB.derivWithin hC (m := ∞) (by simp)).continuousOn
  have hrawInt : IntervalIntegrable raw volume a b := hraw.intervalIntegrable_of_Icc hab.le
  have hdBInt : IntervalIntegrable dB volume a b := hdB.intervalIntegrable_of_Icc hab.le
  have hid (s : ℝ) (hs : s ∈ Ioo a b) : raw s = dB s + idx s :=
    secondVariation_density_identity hpotential htime V D heuler hs
  apply (hrawInt.sub hdBInt).congr_uIoo
  intro s hs
  rw [uIoo_of_le hab.le] at hs
  have h := hid s hs
  linarith

theorem hasDerivAt_secondVariation {J : Set ℝ} {F : RicciFlow 2 M J}
    {T τ₁ τ₂ : ℝ}
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (hclock : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J))
    (htime : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂), T - r ^ 2 ∈ interior J)
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V)
    (heuler : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      ∀ W : TangentSpace (𝓡 2) (V.baseSquareCurve r),
        regularizedEulerResidual F T V.baseSquareCurve
          (sqrtParameterInterval τ₁ τ₂) D.velocity_extension r W = 0) :
    HasDerivAt (fun u ↦ deriv (variationSquareAction V) u)
      (secondVariationBoundaryTerm V D + secondVariationIndexForm V D) 0 := by
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  let C := sqrtParameterInterval τ₁ τ₂
  let raw := fun s ↦ variationParameterDeriv C V.parameterDomain
    (variationParameterDeriv C V.parameterDomain (variationActionDensity V)) (s, 0)
  let B := variationAccelerationBoundaryPair V D
  let dB := derivWithin B C
  let idx := secondVariationIndexDensity V D
  have hab : a < b := Real.sqrt_lt_sqrt p.nonnegative p.ordered
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hab
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hraw : ContinuousOn raw C :=
    (variationParameterDeriv_contDiffOn hC isOpen_Ioo _
      (variationParameterDeriv_contDiffOn hC isOpen_Ioo _
        (variationActionDensity_contDiffOn hpotential V))).continuousOn.comp
          (continuousOn_id.prodMk continuousOn_const) (fun s hs ↦ ⟨hs, hzero⟩)
  have hB : ContDiffOn ℝ ∞ B C := variationAccelerationBoundaryPair_contDiffOn V D hclock
  have hdB : ContinuousOn dB C := (hB.derivWithin hC (m := ∞) (by simp)).continuousOn
  have hrawInt : IntervalIntegrable raw volume a b := hraw.intervalIntegrable_of_Icc hab.le
  have hdBInt : IntervalIntegrable dB volume a b := hdB.intervalIntegrable_of_Icc hab.le
  have hid (s : ℝ) (hs : s ∈ Ioo a b) : raw s = dB s + idx s :=
    secondVariation_density_identity hpotential htime V D heuler hs
  have hidxInt : IntervalIntegrable idx volume a b := by
    apply (hrawInt.sub hdBInt).congr_uIoo
    intro s hs
    rw [uIoo_of_le hab.le] at hs
    have h := hid s hs
    linarith
  have hFTC : (∫ s in a..b, dB s) = B b - B a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hB.continuousOn
      (fun s hs ↦ (((hB s (Ioo_subset_Icc_self hs)).differentiableWithinAt
        (by simp)).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hs.1 hs.2)) hdBInt
  have hvalue : (∫ s in a..b, raw s) =
      secondVariationBoundaryTerm V D + secondVariationIndexForm V D := by
    calc
      (∫ s in a..b, raw s) = ∫ s in a..b, dB s + idx s :=
        intervalIntegral.integral_congr_Ioo_of_le hab.le hid
      _ = (∫ s in a..b, dB s) + ∫ s in a..b, idx s :=
        intervalIntegral.integral_add hdBInt hidxInt
      _ = _ := by rw [hFTC, secondVariationBoundaryTerm_eq_accelerationPair]; rfl
  have h := hasDerivAt_deriv_variationSquareAction_integral hpotential V hzero
  change HasDerivAt (fun u ↦ deriv (variationSquareAction V) u) (∫ s in a..b, raw s) 0 at h
  rwa [hvalue] at h

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
