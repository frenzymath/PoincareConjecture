import PoincareConjecture.Proofs.M14.Sec6_3_InitialAction
import PoincareConjecture.Proofs.M14.Sec6_1_SquareDensity
import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem initialValueAction_hasDerivWithinAt
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T s : ℝ} {x y : G.Point} {Z : G.Horizontal x} (hs : 0 < s)
    (P : M14SquareRootInitialValuePath G T (s ^ 2) x y Z) :
    HasDerivWithinAt (initialValueAction G T x Z)
      ((1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (P.square_path.curve s)
        (P.square_path.horizontal_velocity s) (P.square_path.horizontal_velocity s) +
          2 * s ^ 2 * horizontalScalarCurvature G.leafwise (P.square_path.curve s))
      {r | (Z, r) ∈ initialValueDomain G T x} s := by
  obtain ⟨d, hsd, hnear, z, Q, hQP⟩ :=
    exists_initialValuePath_extension_neighborhood hM04 hM12 P
  rw [Real.sqrt_sq hs.le] at hsd hnear
  have hd : 0 < d := hs.trans_le hsd
  have hC : M14SqrtParameterInterval 0 (s ^ 2) = Icc 0 s := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hs.le]
  have hD : M14SqrtParameterInterval 0 (d ^ 2) = Icc 0 d := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hd.le]
  have hcont : ContinuousOn (squareRootLIntegrand Q.square_path) (Icc 0 d) := by
    simpa only [hD] using (squareRootLIntegrand_contDiffOn hM12 Q.square_path).continuousOn
  have hint : IntervalIntegrable (squareRootLIntegrand Q.square_path) volume 0 s :=
    (hcont.mono (Icc_subset_Icc le_rfl hsd)).intervalIntegrable_of_Icc hs.le
  let : Fact (s ∈ Icc 0 d) := ⟨⟨hs.le, hsd⟩⟩
  have hderiv := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc 0 d) (t := Icc 0 d) hint
    (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hcont s ⟨hs.le, hsd⟩)
  have hprimitive : ∀ r ∈ Icc 0 d,
      initialValueAction G T x Z r = ∫ t in 0..r, squareRootLIntegrand Q.square_path t := by
    intro r hr
    exact initialValueAction_eq_integral_prefix hM04 hM12 Q
      (by simpa only [Real.sqrt_sq hd.le] using hr)
  have haction := hderiv.congr_of_mem hprimitive ⟨hs.le, hsd⟩
  have hbase : G.spacetime.timeFunction x = T := by
    simpa only [GeneralizedFlowSpacetime.timeFunction, sub_zero] using P.path.base_time
  have hnearD : Icc 0 d ∈ 𝓝[{r | (Z, r) ∈ initialValueDomain G T x}] s :=
    nhdsWithin_mono s (fun _ hr => initialValueDomain_admissible hbase hr) hnear
  have hfull := haction.mono_of_mem_nhdsWithin hnearD
  have heq : EqOn Q.square_path.curve P.square_path.curve (Icc 0 s) := by
    simpa only [hC] using hQP
  have hsubQ : Icc 0 s ⊆ M14SqrtParameterInterval 0 (d ^ 2) :=
    hD ▸ Icc_subset_Icc le_rfl hsd
  have hsubP : Icc 0 s ⊆ M14SqrtParameterInterval 0 (s ^ 2) := hC ▸ Subset.refl _
  have hdensity := squareRootLIntegrand_eq_on_subset Q.square_path P.square_path
    hsubQ hsubP heq ⟨hs.le, le_rfl⟩ (uniqueDiffOn_Icc hs s ⟨hs.le, le_rfl⟩)
  rw [hdensity] at hfull
  simpa only [squareRootLIntegrand, add_comm] using hfull

end PoincareConjecture.M14
