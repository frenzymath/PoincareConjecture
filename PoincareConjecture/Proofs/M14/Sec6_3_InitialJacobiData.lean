import PoincareConjecture.Proofs.M14.Sec6_3_InitialDifferentialSmooth
import PoincareConjecture.Proofs.M14.Sec6_4_IndexJacobi

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
  (P : M14SquareRootInitialValuePath G T τ x y Z) (W : G.Horizontal x)

private theorem transport_zero {q r : G.Point} (h : q = r) :
    (h ▸ (0 : G.Horizontal q) : G.Horizontal r) = 0 := by
  cases h
  rfl

noncomputable def initialValuePath_differentialField (r : ℝ) :
    G.Horizontal (P.square_path.curve r) := by
  classical
  exact if hr : r ∈ M14SqrtParameterInterval 0 τ then
    (initialValueCurve_eqOn_square hM04 hM12 P hr) ▸ initialValueDifferential G T x Z r W
  else 0

theorem initialValuePath_differentialField_heq {r : ℝ}
    (hr : r ∈ M14SqrtParameterInterval 0 τ) :
    HEq (initialValuePath_differentialField hM04 hM12 P W r)
      (initialValueDifferential G T x Z r W) := by
  unfold initialValuePath_differentialField
  rw [dif_pos hr]
  exact eqRec_heq _ _

theorem initialValuePath_differentialField_contMDiffOn :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun r => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (P.square_path.curve r)
          (initialValuePath_differentialField hM04 hM12 P W r))
      (M14SqrtParameterInterval 0 τ) := by
  have hbase : G.spacetime.timeFunction x = T := by
    simpa only [GeneralizedFlowSpacetime.timeFunction, sub_zero] using P.path.base_time
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr P.path.tau_lt
  have hsurv : (Z, Real.sqrt τ) ∈ initialValueDomain G T x := by
    refine Or.inr ⟨hs, y, ?_⟩
    rw [Real.sq_sqrt P.path.tau_lt.le]
    exact ⟨P⟩
  have hsm := initialValueDifferential_field_contMDiffOn hM04 hM12 hbase hs hsurv W
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 (Real.sqrt τ) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero]
  rw [← hC] at hsm
  apply hsm.congr
  intro r hr
  exact Bundle.TotalSpace.ext (initialValueCurve_eqOn_square hM04 hM12 P hr).symm
    (initialValuePath_differentialField_heq hM04 hM12 P W hr)

theorem initialValuePath_differentialField_zero :
    initialValuePath_differentialField hM04 hM12 P W 0 = 0 := by
  have h0 : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, mem_Icc, le_refl, true_and]
    exact Real.sqrt_nonneg τ
  have hz : initialValueDifferential G T x Z 0 W = 0 := by
    change G.spacetime.horizontalProjection _
      (M14InitialVectorDerivative G (initialValueCurve G T x) 0 Z W) = 0
    rw [initialValueCurve_initialVectorDerivative_zero]
    simp only [zero_apply, map_zero]
  unfold initialValuePath_differentialField
  rw [dif_pos h0, hz]
  exact transport_zero _

noncomputable def initialValuePath_differentialData :
    M14JacobiFieldData G P.square_path.curve (M14SqrtParameterInterval 0 τ) := by
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 (Real.sqrt τ) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero]
  have hE : Nonempty (M14PullbackExtension G P.square_path.curve
      (M14SqrtParameterInterval 0 τ) (initialValuePath_differentialField hM04 hM12 P W)) := by
    rw [hC]
    apply exists_pullbackExtension_Icc (Real.sqrt_pos.mpr P.path.tau_lt)
    rw [← hC]
    exact initialValuePath_differentialField_contMDiffOn hM04 hM12 P W
  exact jacobiFieldDataOfExtension
    (hM12.coordinate_gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise)
    (Classical.choice hE)

end PoincareConjecture.M14
