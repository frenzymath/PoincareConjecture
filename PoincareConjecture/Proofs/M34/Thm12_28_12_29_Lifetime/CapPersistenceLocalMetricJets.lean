import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceChartJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceProductJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceTensorReadout
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCoordinateSmooth
import PoincareConjecture.Proofs.M34.Mathlib.BilinearPullbackJetBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def capCoefficientEvaluation (a b : Fin 3) :
    (E₃ →L[ℝ] E₃ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
    (ContinuousLinearMap.apply ℝ (E₃ →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ a))

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "OrdinaryFlow" => ordinaryChapter11Flow (I := I) (F := F) R

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem ordinaryChapter11_eventually_chart_neck_metricJets
    (p : ℕ → (OrdinaryFlow).point) (hp : ∀ k, 0 < (OrdinaryFlow).scalar (p k))
    (hd : Tendsto (fun k => (OrdinaryFlow).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence (fixedFlowBlowupSequence (OrdinaryFlow) p hp hd) J)
    (hJ : UniqueDiffOn ℝ J) (N : EpsilonNeck (C.limit.flow.metric 0))
    (m : ℕ) (hm : m + 1 ≤ Nat.floor N.epsilon⁻¹)
    (a : C.limit.sliceCarrier.carrier) {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) a).target) (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ k : ℕ in atTop, ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ (extChartAt (𝓡 3) a).source →
      (extChartAt (𝓡 3) a) (N.coordinate_map (q, s)) ∈ H →
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
            (generalizedCylinderPullback (C.embedding k) N.coordinate_map 0)
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, s)‖ < rho := by
  classical
  let : T2Space C.limit.carrier.carrier := C.limit.carrier.t2Space
  let c := extChartAt (𝓡 3) a
  obtain ⟨D, hD, hDbound⟩ := N.exists_capPersistence_chart_jet_bound m hm a hH hHt
  choose B hB hbound using fun j : Fin (m + 1) =>
    exists_bilinear_pullback_jet_bound (E := E₃) (F := E₃) (G := ℝ) j hD
  let B0 : ℝ := ∑ j : Fin (m + 1), B j
  let E0 : ℝ := ∑ ij : Fin 3 × Fin 3, ‖capCoefficientEvaluation ij.1 ij.2‖
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
    have hh : (A0 + 1) * eta = rho := by dsimp [eta]; field_simp
    nlinarith
  have hcompact : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm a).mono hHt)
  obtain ⟨j0, hj0⟩ := C.exists_exhaustion_superset hcompact
  have hdom : ({0} ×ˢ H) ⊆ {z | z ∈ blowupMetricChartDomain C.limit a ∧
      c.symm z.2 ∈ C.exhaustion.space j0} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    rcases mem_singleton_iff.mp ht with rfl
    exact ⟨⟨C.limit.zero_mem, hHt hy⟩, hj0 ⟨y, hy, rfl⟩⟩
  obtain ⟨k0, hjk0, hk0⟩ := ordinaryChapter11_uniform_bilinear_metricJets
    R p hp hd C hJ a j0 m ({0} ×ˢ H) (isCompact_singleton.prod hH) hdom eta heta
  filter_upwards [eventually_ge_atTop k0] with k hk q s hs hsource hcenter j hj i l
  let φ := N.capPersistenceEuclideanMap q s
  let f := c ∘ φ
  let T : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := fun y =>
    blowupCoordinateBilinear (C.embedding k) a 0 y - limitCoordinateBilinear C.limit a 0 y
  have hφ0 : φ 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  have hf0 : f 0 = c (N.coordinate_map (q, s)) := congrArg c hφ0
  have hc := (hk0 k hk).1
    (show (0, c (N.coordinate_map (q, s))) ∈ ({0} : Set ℝ) ×ˢ H from ⟨rfl, hcenter⟩)
  have hcapture : c.symm (f 0) ∈ C.exhaustion.space k := by
    rw [hf0]
    exact C.exhaustion.space_increasing (hjk0.trans hk) (hj0 ⟨_, hcenter, rfl⟩)
  have hφ : ContMDiffAt (𝓡 3) (𝓡 3) ∞ φ 0 :=
    N.capPersistenceEuclideanMap_contMDiffAt q s (by simpa using hs)
  have hchart : φ 0 ∈ c.source := by rw [hφ0]; exact hsource
  have hf : ContDiffAt ℝ ∞ f 0 := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source a).mem_nhds hchart)).comp 0 hφ)
  have hT : ContDiffAt ℝ ∞ T (f 0) :=
    (ordinaryChapter11CoordinateBilinear_contDiffAt R (C.embedding k)
      (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected hc.1 a
        ⟨by rw [hf0]; exact hc.2, hcapture⟩).sub
      (limitCoordinateBilinear_contDiffAt C.limit a C.limit.zero_mem
        (by rw [hf0]; exact hHt hcenter))
  have hTjet (r : ℕ) (hr : r ≤ j) : ‖iteratedFDeriv ℝ r T (f 0)‖ ≤ eta := by
    rw [hf0]
    exact ((hk0 k hk).2 (0, c (N.coordinate_map (q, s))) ⟨rfl, hcenter⟩ r
      (hr.trans hj)).le
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  let P := fun x => (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hP : ContDiffAt ℝ ∞ P 0 := hf.bilinearPullback hT
  have hPjet : ‖iteratedFDeriv ℝ j P 0‖ ≤ B j' * eta :=
    hbound j' f T 0 hf hT (fun r hr => hDbound q s hs hsource hcenter r (by omega))
      eta heta.le hTjet
  let F0 : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient
      (generalizedCylinderPullback (C.embedding k) N.coordinate_map 0) (chartAt E₂ q) y i l -
    roundCylinderTensorCoefficient
      (roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map) (chartAt E₂ q) y i l
  have heq : (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, s)))
      =ᶠ[𝓝 (0 : E₃)] (capCoefficientEvaluation i l) ∘ P := by
    have hnear := hφ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds hchart)
    have haxis : ∀ᶠ x : E₃ in 𝓝 0,
        x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      have hcont : ContinuousAt (fun x : E₃ => x 2 + s) 0 :=
        ((EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous.add continuous_const).continuousAt
      exact hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa using hs))
    filter_upwards [hnear, haxis] with x hx hxaxis
    exact capPersistence_coefficient_difference_fixed_chart
      (C.embedding k) N q s a hc.1 hxaxis hx i l
  have hscalar := (capCoefficientEvaluation i l).contDiff.contDiffAt.comp 0 hP
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hE : ‖capCoefficientEvaluation i l‖ ≤ E0 :=
    Finset.single_le_sum (fun ij _ => norm_nonneg (capCoefficientEvaluation ij.1 ij.2))
      (Finset.mem_univ (i, l))
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, s))) 0‖ ≤
        E0 * B0 * eta := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖capCoefficientEvaluation i l‖ * ‖iteratedFDeriv ℝ j P 0‖ :=
        (capCoefficientEvaluation i l).norm_iteratedFDeriv_comp_left hP
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
        (fun x : E₃ => F0 (capPersistenceProductCoordinates x + (0, s))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 s j
        (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (E0 * B0 * eta) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = A0 * eta := by dsimp [A0]; ring
    _ < rho := hsmall

end PoincareConjecture.M34
