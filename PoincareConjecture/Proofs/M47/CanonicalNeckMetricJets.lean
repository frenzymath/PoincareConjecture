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

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]

theorem neck_metric_coefficient_difference_fixed_chart
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    (g h : RiemannianMetric 3 M) (q : UnitTwoSphere) (z : ℝ) (a : M)
    {x : E₃} (hx : x 2 + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (ha : N.capPersistenceEuclideanMap q z x ∈ (extChartAt (𝓡 3) a).source)
    (i l : Fin 3) :
    let phi := N.capPersistenceEuclideanMap q z
    let f := (extChartAt (𝓡 3) a) ∘ phi
    roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, z)) i l -
      roundCylinderTensorCoefficient (roundCylinderPullback h N.coordinate_map)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, z)) i l =
      ((g.pullbackCoefficients (extChartAt (𝓡 3) a).symm (f x) -
          h.pullbackCoefficients (extChartAt (𝓡 3) a).symm (f x)).bilinearComp
        (fderiv ℝ f x) (fderiv ℝ f x))
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ l) := by
  dsimp only
  have hphi := (N.capPersistenceEuclideanMap_contMDiffAt q z hx).mdifferentiableAt (by simp)
  have hg := g.capPersistence_chart_pullback a hphi ha
  have hh := h.capPersistence_chart_pullback a hphi ha
  have hs := N.capPersistence_tensor_coefficient (fun y v w => g.inner y v w) q z hx i l
  have ht := N.capPersistence_tensor_coefficient (fun y v w => h.inner y v w) q z hx i l
  have hread := congrArg₂ (fun A B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ =>
    A (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ l) -
      B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ l)) hg hh
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply] at hread ⊢
  exact (congrArg₂ (fun v w : ℝ => v - w) hs ht).trans hread.symm

private noncomputable def neckCoefficientEvaluation (i l : Fin 3) :
    (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ l)).comp
    (ContinuousLinearMap.apply ℝ (E₃ →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ i))

theorem eventually_chart_neck_metric_jets [T2Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : EpsilonNeck (F.metric t.val))
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    (p : M) {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) p).target) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, z) ∈ (extChartAt (𝓡 3) p).source →
      (extChartAt (𝓡 3) p) (N.coordinate_map (q, z)) ∈ H →
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s.val) N.coordinate_map)
              (chartAt E₂ q) y i l -
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t.val) N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let c := extChartAt (𝓡 3) p
  obtain ⟨D, hD, hDbound⟩ := neck_chart_map_jets_at_recorded_order N m hm p hH hHt
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound (E := E₃) (F := E₃) (G := ℝ) j hD
  let B0 : ℝ := ∑ j : Fin (m + 1), B j
  let E0 : ℝ := ∑ il : Fin 3 × Fin 3, ‖neckCoefficientEvaluation il.1 il.2‖
  let L0 : ℝ := max 1 ‖capPersistenceEuclideanCoordinates‖
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun j _ => hB j
  have hE0 : 0 ≤ E0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL0 : 1 ≤ L0 := le_max_left _ _
  let A0 := E0 * B0 * L0 ^ m
  have hA0 : 0 ≤ A0 := mul_nonneg (mul_nonneg hE0 hB0)
    (pow_nonneg (zero_le_one.trans hL0) _)
  let eta := rho / (A0 + 1)
  have heta : 0 < eta := div_pos hrho (by positivity)
  have hsmall : A0 * eta < rho := by
    have heq : (A0 + 1) * eta = rho := by dsimp only [eta]; field_simp
    nlinarith
  filter_upwards [metric_jets_uniform_near_time_on_compact hab F
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hH hHt t m heta]
    with s hs q z hz hsource hcenter j hj i l
  let phi := N.capPersistenceEuclideanMap q z
  let f := c ∘ phi
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    (F.metric s.val).pullbackCoefficients c.symm y -
      (F.metric t.val).pullbackCoefficients c.symm y
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
    ((F.metric s.val).contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htarget) |>.sub
      (((F.metric t.val).contDiffOn_chartCoefficients p).contDiffAt
        ((isOpen_extChartAt_target p).mem_nhds htarget))
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f 0)‖ ≤ eta := by
    rw [hf0]
    exact (hs _ hcenter r (hr.trans hj)).le
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let P := fun x => (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hP : ContDiffAt ℝ ∞ P 0 := hf.bilinearPullback hT
  have hPjet : ‖iteratedFDeriv ℝ j P 0‖ ≤ B j' * eta :=
    hbound j' f T 0 hf hT (fun r hr => hDbound q z hz hsource hcenter r (by omega))
      eta heta.le hTjet
  let F0 : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s.val) N.coordinate_map)
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t.val) N.coordinate_map)
        (chartAt E₂ q) y i l
  have heq : (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z)))
      =ᶠ[𝓝 (0 : E₃)] (neckCoefficientEvaluation i l) ∘ P := by
    have hnear := hphi.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hchart)
    have haxis : ∀ᶠ x : E₃ in 𝓝 0,
        x 2 + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      have hc : ContinuousAt (fun x : E₃ => x 2 + z) 0 :=
        ((EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
      exact hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hz))
    filter_upwards [hnear, haxis] with x hx hxaxis
    exact neck_metric_coefficient_difference_fixed_chart N (F.metric s.val) (F.metric t.val)
      q z p hxaxis hx i l
  have hscalar := (neckCoefficientEvaluation i l).contDiff.contDiffAt.comp 0 hP
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hE : ‖neckCoefficientEvaluation i l‖ ≤ E0 :=
    Finset.single_le_sum (fun il _ => norm_nonneg (neckCoefficientEvaluation il.1 il.2))
      (Finset.mem_univ (i, l))
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ ≤ E0 * B0 * eta := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖neckCoefficientEvaluation i l‖ * ‖iteratedFDeriv ℝ j P 0‖ :=
        (neckCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left hP
          (by exact_mod_cast le_top)
      _ ≤ E0 * (B j' * eta) := mul_le_mul hE hPjet (norm_nonneg _) hE0
      _ ≤ E0 * (B0 * eta) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun r _ => hB r) (Finset.mem_univ j')) heta.le) hE0
      _ = _ := by ring
  have hlin : ‖capPersistenceEuclideanCoordinates‖ ^ j ≤ L0 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hL0 hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j
        (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, z))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 z j
        (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (E0 * B0 * eta) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = A0 * eta := by dsimp only [A0]; ring
    _ < rho := hsmall

theorem eventually_neck_metric_jets [T3Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : EpsilonNeck (F.metric t.val))
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {K : Set M} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s.val) N.coordinate_map)
              (chartAt E₂ q) y i l -
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t.val) N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let P (s : Icc a b) (q : UnitTwoSphere) (z : ℝ) : Prop :=
    ∀ j ≤ m, ∀ i l : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s.val) N.coordinate_map)
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t.val) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, z)‖ < rho
  have hlocal (p : M) : ∃ U : Set M, U ∈ 𝓝 p ∧
      ∀ᶠ s : Icc a b in 𝓝 t, ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → N.coordinate_map (q, z) ∈ U → P s q z := by
    let c := extChartAt (𝓡 3) p
    obtain ⟨H, hH, hpH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) p) (mem_extChartAt_target (I := 𝓡 3) p)
    let U := c.source ∩ c ⁻¹' H
    have hU : U ∈ 𝓝 p := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 3) p)
      ((continuousAt_extChartAt (I := 𝓡 3) p).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hpH))
    refine ⟨U, hU, ?_⟩
    filter_upwards [eventually_chart_neck_metric_jets (M := M) hab F t N m hm p hH hHt hrho]
      with s hs q z hz hx
    exact hs q z hz hx.1 hx.2
  choose U hU hbound using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover U (fun p _ => hU p)
  filter_upwards [S.eventually_all.mpr (fun p _ => hbound p)] with s hs q z hz
  obtain ⟨p, hpS, hxp⟩ : ∃ p ∈ S, N.coordinate_map (q, z) ∈ U p := by
    simpa only [mem_iUnion, exists_prop] using hcover (hNK (N.coordinate_map_mem_of_axial_mem hz))
  exact hs p hpS q z hz hxp

end PoincareConjecture.Proofs.M47
