import PoincareConjecture.Proofs.M47.CanonicalNeckMetricJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def neckChartCoefficientEvaluation (i l : Fin 3) :
    (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ l)).comp
    (ContinuousLinearMap.apply ℝ (E₃ →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ i))

private theorem neckChartCoefficientEvaluation_norm_le (i l : Fin 3) :
    ‖neckChartCoefficientEvaluation i l‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa only [neckChartCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one,
    mul_one, one_mul] using B.le_opNorm₂
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ l)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]



theorem exists_neck_chart_coefficient_difference_bound
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    (p : M) {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g h : RiemannianMetric 3 M) (eta : ℝ), 0 ≤ eta →
      (∀ x ∈ H, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y =>
        g.pullbackCoefficients (extChartAt (𝓡 3) p).symm y -
          h.pullbackCoefficients (extChartAt (𝓡 3) p).symm y) x‖ ≤ eta) →
      ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        N.coordinate_map (q, z) ∈ (extChartAt (𝓡 3) p).source →
        (extChartAt (𝓡 3) p) (N.coordinate_map (q, z)) ∈ H →
        ∀ j ≤ m, ∀ i l : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
              (chartAt E₂ q) y i l -
            roundCylinderTensorCoefficient (roundCylinderPullback h N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z)‖ ≤ C * eta := by
  classical
  obtain ⟨D, hD, hDbound⟩ := neck_chart_map_jets_at_recorded_order N m hm p hH hHt
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound (E := E₃) (F := E₃) (G := ℝ) j hD
  let B0 : ℝ := ∑ j : Fin (m + 1), B j
  let L0 : ℝ := max 1 ‖capPersistenceEuclideanCoordinates‖
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun j _ => hB j
  have hL0 : 1 ≤ L0 := le_max_left _ _
  refine ⟨B0 * L0 ^ m, mul_nonneg hB0 (pow_nonneg (zero_le_one.trans hL0) _), ?_⟩
  intro g h eta heta hjet q z hz hsource hcenter j hj i l
  let c := extChartAt (𝓡 3) p
  let phi := N.capPersistenceEuclideanMap q z
  let f := c ∘ phi
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    g.pullbackCoefficients c.symm y - h.pullbackCoefficients c.symm y
  have hphi0 : phi 0 = N.coordinate_map (q, z) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q z)
  have hf0 : f 0 = c (N.coordinate_map (q, z)) := congrArg c hphi0
  have hphi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ phi 0 :=
    N.capPersistenceEuclideanMap_contMDiffAt q z (by simpa using hz)
  have hchart : phi 0 ∈ c.source := by rw [hphi0]; exact hsource
  have hf : ContDiffAt ℝ ∞ f 0 := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := p) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source p).mem_nhds hchart)).comp 0 hphi)
  have htarget : f 0 ∈ c.target := by rw [hf0]; exact hHt hcenter
  have hT : ContDiffAt ℝ ∞ T (f 0) :=
    ((g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)).sub
      ((h.contDiffOn_chartCoefficients p).contDiffAt
        ((isOpen_extChartAt_target p).mem_nhds htarget))
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f 0)‖ ≤ eta := by
    rw [hf0]
    exact hjet _ hcenter r (hr.trans hj)
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let P := fun x => (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hP : ContDiffAt ℝ ∞ P 0 := hf.bilinearPullback hT
  have hPjet : ‖iteratedFDeriv ℝ j P 0‖ ≤ B j' * eta :=
    hbound j' f T 0 hf hT (fun r hr => hDbound q z hz hsource hcenter r (by omega))
      eta heta hTjet
  let F0 : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback h N.coordinate_map)
        (chartAt E₂ q) y i l
  have heq : (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z)))
      =ᶠ[𝓝 (0 : E₃)] (neckChartCoefficientEvaluation i l) ∘ P := by
    have hnear := hphi.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hchart)
    have haxis : ∀ᶠ x : E₃ in 𝓝 0, x 2 + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      have hc : ContinuousAt (fun x : E₃ => x 2 + z) 0 :=
        ((EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
      exact hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hz))
    filter_upwards [hnear, haxis] with x hx hxaxis
    exact neck_metric_coefficient_difference_fixed_chart N g h q z p hxaxis hx i l
  have hscalar := (neckChartCoefficientEvaluation i l).contDiff.contDiffAt.comp 0 hP
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ ≤ B0 * eta := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖neckChartCoefficientEvaluation i l‖ * ‖iteratedFDeriv ℝ j P 0‖ :=
        (neckChartCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left hP
          (by exact_mod_cast le_top)
      _ ≤ 1 * ‖iteratedFDeriv ℝ j P 0‖ := mul_le_mul_of_nonneg_right
        (neckChartCoefficientEvaluation_norm_le i l) (norm_nonneg _)
      _ ≤ B j' * eta := by simpa only [one_mul] using hPjet
      _ ≤ B0 * eta := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) heta
  have hlin : ‖capPersistenceEuclideanCoordinates‖ ^ j ≤ L0 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hL0 hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j
        (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 z j
        (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (B0 * eta) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (mul_nonneg hB0 heta)
    _ = (B0 * L0 ^ m) * eta := by ring

end PoincareConjecture.Proofs.M47
