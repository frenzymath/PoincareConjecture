import PoincareConjecture.Proofs.M47.CanonicalNeckMapJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceProductJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceTensorReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

namespace PoincareConjecture.M47

open M34

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private noncomputable def capNeckEvaluation (i l : Fin 3) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ l)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ i))




theorem exists_cap_neck_bilinear_error_jet_bound {g : RiemannianMetric 3 E}
    (N : EpsilonNeck g) (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {K : Set E} (hK : IsCompact K) (hNK : N.carrier ⊆ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : E → E →L[ℝ] E →L[ℝ] ℝ,
      (∀ x ∈ N.carrier, ContDiffAt ℝ ∞ T x) →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ x ∈ N.carrier, ∀ j ≤ m, ‖iteratedFDeriv ℝ j T x‖ ≤ rho) →
      ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient
          (fun w v v' => T (N.coordinate_map w)
            (mfderiv Ic (𝓡 3) N.coordinate_map w v)
            (mfderiv Ic (𝓡 3) N.coordinate_map w v'))
          (chartAt E₂ q) y i l) (0, z)‖ ≤ C * rho := by
  classical
  obtain ⟨D, hD, hDbound⟩ := Proofs.M47.neck_chart_map_jets_at_recorded_order
    N m hm (0 : E) hK (by simp)
  have hmap (q : UnitTwoSphere) (z : ℝ)
      (hz : z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (j : ℕ) (hj : j ≤ m + 1) :
      ‖iteratedFDeriv ℝ j (N.capPersistenceEuclideanMap q z) 0‖ ≤ D := by
    simpa only [extChartAt_self_eq, modelWithCornersSelf_coe, Function.id_comp] using
      hDbound q z hz (by simp)
        (by simpa [extChartAt_self_eq] using hNK (N.coordinate_map_mem_of_axial_mem hz)) j hj
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound («E» := E) (F := E) (G := ℝ) j hD
  let B0 : ℝ := ∑ j : Fin (m + 1), B j
  let E0 : ℝ := ∑ il : Fin 3 × Fin 3, ‖capNeckEvaluation il.1 il.2‖
  let L0 : ℝ := max 1 ‖capPersistenceEuclideanCoordinates‖
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun j _ => hB j
  have hE0 : 0 ≤ E0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL0 : 1 ≤ L0 := le_max_left _ _
  let C0 := E0 * B0 * L0 ^ m
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg hE0 hB0)
    (pow_nonneg (zero_le_one.trans hL0) _)
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro T hT rho hrho hjet q z hz j hj i l
  let f := N.capPersistenceEuclideanMap q z
  have hf0 : f 0 = N.coordinate_map (q, z) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q z)
  have hcenter : f 0 ∈ N.carrier := hf0 ▸ N.coordinate_map_mem_of_axial_mem hz
  have hf : ContDiffAt ℝ ∞ f 0 := contMDiffAt_iff_contDiffAt.mp
    (N.capPersistenceEuclideanMap_contMDiffAt q z (by simpa using hz))
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let P := fun x => (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hP : ContDiffAt ℝ ∞ P 0 := hf.bilinearPullback (hT _ hcenter)
  have hPjet : ‖iteratedFDeriv ℝ j P 0‖ ≤ B j' * rho :=
    hbound j' f T 0 hf (hT _ hcenter) (fun r hr => hmap q z hz r (by omega))
      rho hrho (fun r hr => hjet _ hcenter r (hr.trans hj))
  let F0 : RoundCylinderCoordinates → ℝ := fun y => roundCylinderTensorCoefficient
    (fun w v v' => T (N.coordinate_map w)
      (mfderiv Ic (𝓡 3) N.coordinate_map w v)
      (mfderiv Ic (𝓡 3) N.coordinate_map w v')) (chartAt E₂ q) y i l
  have heq : (fun x : E => F0 (capPersistenceProductCoordinates x + (0, z)))
      =ᶠ[𝓝 (0 : E)] (capNeckEvaluation i l) ∘ P := by
    have hc : ContinuousAt (fun x : E => x 2 + z) 0 :=
      ((EuclideanSpace.proj 2 : E →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
    filter_upwards [hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hz))]
      with x hx
    have h := N.capPersistence_tensor_coefficient (fun y v w => T y v w) q z hx i l
    simp only [mfderiv_eq_fderiv] at h
    convert h using 1
    simp [capNeckEvaluation, P, f, ContinuousLinearMap.bilinearComp_apply]
    rfl
  have hscalar := (capNeckEvaluation i l).contDiff.contDiffAt.comp 0 hP
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hE : ‖capNeckEvaluation i l‖ ≤ E0 :=
    Finset.single_le_sum (fun il _ => norm_nonneg (capNeckEvaluation il.1 il.2))
      (Finset.mem_univ (i, l))
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ ≤ E0 * B0 * rho := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖capNeckEvaluation i l‖ * ‖iteratedFDeriv ℝ j P 0‖ :=
        (capNeckEvaluation i l).norm_iteratedFDeriv_comp_left hP (by exact_mod_cast le_top)
      _ ≤ E0 * (B j' * rho) := mul_le_mul hE hPjet (norm_nonneg _) hE0
      _ ≤ E0 * (B0 * rho) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) hrho) hE0
      _ = _ := by ring
  have hlin : ‖capPersistenceEuclideanCoordinates‖ ^ j ≤ L0 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hL0 hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j
        (fun x : E => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 z j
        (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (E0 * B0 * rho) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = C0 * rho := by dsimp only [C0]; ring
    _ ≤ (C0 + 1) * rho := mul_le_mul_of_nonneg_right (by linarith) hrho

end PoincareConjecture.M47
