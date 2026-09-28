import PoincareConjecture.Proofs.M08.SecondVariationIdentity

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_secondVariation {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) (R : RegularizedLGeodesicData p) :
    HasDerivAt (fun u ↦ deriv (variationLLength V) u)
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
        (variationActionDensity_contDiffOn hM04 V))).continuousOn.comp
          (continuousOn_id.prodMk continuousOn_const) (fun s hs ↦ ⟨hs, hzero⟩)
  have hB : ContDiffOn ℝ ∞ B C := variationAccelerationBoundaryPair_contDiffOn V D
  have hdB : ContinuousOn dB C := (hB.derivWithin hC (m := ∞) (by simp)).continuousOn
  have hrawInt : IntervalIntegrable raw volume a b := hraw.intervalIntegrable_of_Icc hab.le
  have hdBInt : IntervalIntegrable dB volume a b := hdB.intervalIntegrable_of_Icc hab.le
  have hid (s : ℝ) (hs : s ∈ Ioo a b) : raw s = dB s + idx s :=
    secondVariation_density_identity hM04 V D R hs
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
  have h := hasDerivAt_deriv_variationLLength_integral hM04 V hzero
  change HasDerivAt (fun u ↦ deriv (variationLLength V) u) (∫ s in a..b, raw s) 0 at h
  rwa [hvalue] at h

theorem exists_secondVariation {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (R : RegularizedLGeodesicData p) :
    ∃ D : LVariationDerivativeData V, ∃ q : ℝ,
      HasDerivAt (fun u ↦ deriv (variationLLength V) u) q 0 ∧
        q = secondVariationBoundaryTerm V D + secondVariationIndexForm V D := by
  obtain ⟨D⟩ := exists_variationDerivativeData V
  exact ⟨D, _, hasDerivAt_secondVariation hM04 V D R, rfl⟩

end PoincareConjecture.M08
