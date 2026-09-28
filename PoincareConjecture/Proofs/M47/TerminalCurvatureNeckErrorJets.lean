import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckChartError
import PoincareConjecture.Proofs.M47.TerminalCurvatureBoundedMovingPullback
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceProductJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u v

namespace PoincareConjecture.M47

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private noncomputable def terminalNeckEvaluation (a b : Fin 3) :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ a))



theorem terminalCurvature_exists_neck_chart_error_constant_uniform
    (m : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Type u) (X : Type v)
      [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace E M] [ChartedSpace E X]
      [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
      (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
      (h : RiemannianMetric 3 X) (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞),
      N.carrier ⊆ psi.source →
      ∀ (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
        (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ c.source →
      let f := (c : M → E) ∘ N.capPersistenceEuclideanMap q s
      let B := fun y => N.scale⁻¹ ^ 2 •
        (h.pullbackCoefficients (psi ∘ c.symm) y - g.pullbackCoefficients c.symm y)
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f 0‖ ≤ D) →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f 0)‖ ≤ rho) →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
              roundCylinderPullback h (psi ∘ N.coordinate_map) z v w)
              (chartAt E₂ q) y a b -
            roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
              roundCylinderPullback g N.coordinate_map z v w)
              (chartAt E₂ q) y a b) (0, s)‖ ≤ C * rho := by
  obtain ⟨B0, hB0, hbound⟩ := terminalCurvature_exists_bounded_pullback_error_constant m hD
  let E0 : ℝ := ∑ ab : Fin 3 × Fin 3, ‖terminalNeckEvaluation ab.1 ab.2‖
  let L0 : ℝ := max 1 ‖capPersistenceEuclideanCoordinates‖
  let C0 : ℝ := E0 * B0 * L0 ^ m
  have hE0 : 0 ≤ E0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hL0 : 1 ≤ L0 := le_max_left _ _
  have hC0 : 0 ≤ C0 := mul_nonneg (mul_nonneg hE0 hB0)
    (pow_nonneg (zero_le_one.trans hL0) _)
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro M X _ _ _ _ _ _ g N h psi hsource c q s hs hc f B hfjet rho hrho hBjet j hj a b
  have hphi0 : N.capPersistenceEuclideanMap q s 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  have hf0 : f 0 = c (N.coordinate_map (q, s)) := congrArg c hphi0
  have hf : ContDiffAt ℝ ∞ f 0 := contMDiffAt_iff_contDiffAt.mp
    ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds
      (hphi0 ▸ hc))).comp 0
        (N.capPersistenceEuclideanMap_contMDiffAt q s (by simpa using hs)))
  have hfmem : f 0 ∈ c.target := hf0 ▸ c.map_source hc
  have hci := c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds hfmem)
  have hinv : c.symm (f 0) = N.coordinate_map (q, s) :=
    (congrArg (fun y : E => c.symm y) hf0).trans (c.left_inv hc)
  have hpsi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ psi (c.symm (f 0)) := by
    rw [hinv]
    exact psi.contMDiffOn_toFun.contMDiffAt
      (psi.open_source.mem_nhds (hsource (N.coordinate_map_mem_of_axial_mem hs)))
  have hBsmooth : ContDiffAt ℝ ∞ B (f 0) :=
    ((h.contDiffAt_pullbackCoefficients (hpsi.comp _ hci)).sub
      (g.contDiffAt_pullbackCoefficients hci)).const_smul (N.scale⁻¹ ^ 2)
  let P := fun x => (B (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hP : ContDiffAt ℝ ∞ P 0 := hf.bilinearPullback hBsmooth
  have hPjet : ‖iteratedFDeriv ℝ j P 0‖ ≤ B0 * rho :=
    hbound f B 0 hf hBsmooth hfjet rho hrho hBjet j hj
  let F0 : RoundCylinderCoordinates → ℝ := fun y =>
    roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback h (psi ∘ N.coordinate_map) z v w) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback g N.coordinate_map z v w) (chartAt E₂ q) y a b
  have heq : (fun x : E => F0 (capPersistenceProductCoordinates x + (0, s)))
      =ᶠ[𝓝 (0 : E)] (terminalNeckEvaluation a b) ∘ P := by
    exact terminalCurvature_neck_chart_error_germ N h psi hsource c q s hs hc a b
  have hscalar := (terminalNeckEvaluation a b).contDiff.contDiffAt.comp 0 hP
  have hFE := hscalar.congr_of_eventuallyEq heq
  have hE : ‖terminalNeckEvaluation a b‖ ≤ E0 :=
    Finset.single_le_sum (fun ab _ => norm_nonneg (terminalNeckEvaluation ab.1 ab.2))
      (Finset.mem_univ (a, b))
  have hFjet : ‖iteratedFDeriv ℝ j
      (fun x : E => F0 (capPersistenceProductCoordinates x + (0, s))) 0‖ ≤
        E0 * B0 * rho := by
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    calc
      _ ≤ ‖terminalNeckEvaluation a b‖ * ‖iteratedFDeriv ℝ j P 0‖ :=
        (terminalNeckEvaluation a b).norm_iteratedFDeriv_comp_left hP
          (by exact_mod_cast le_top)
      _ ≤ E0 * (B0 * rho) := mul_le_mul hE hPjet (norm_nonneg _) hE0
      _ = _ := by ring
  have hlin : ‖capPersistenceEuclideanCoordinates‖ ^ j ≤ L0 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hL0 hj)
  calc
    _ ≤ ‖iteratedFDeriv ℝ j
        (fun x : E => F0 (capPersistenceProductCoordinates x + (0, s))) 0‖ *
          ‖capPersistenceEuclideanCoordinates‖ ^ j :=
      capPersistence_product_jet_le_euclidean F0 s j (hFE.of_le (by exact_mod_cast le_top))
    _ ≤ (E0 * B0 * rho) * L0 ^ m :=
      mul_le_mul hFjet hlin (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = C0 * rho := by dsimp only [C0]; ring
    _ ≤ (C0 + 1) * rho := mul_le_mul_of_nonneg_right (by linarith) hrho

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace E M] [ChartedSpace E X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]



theorem terminalCurvature_exists_neck_chart_error_constant
    (m : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
      (h : RiemannianMetric 3 X) (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞),
      N.carrier ⊆ psi.source →
      ∀ (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
        (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ c.source →
      let f := (c : M → E) ∘ N.capPersistenceEuclideanMap q s
      let B := fun y => N.scale⁻¹ ^ 2 •
        (h.pullbackCoefficients (psi ∘ c.symm) y - g.pullbackCoefficients c.symm y)
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f 0‖ ≤ D) →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f 0)‖ ≤ rho) →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
              roundCylinderPullback h (psi ∘ N.coordinate_map) z v w)
              (chartAt E₂ q) y a b -
            roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
              roundCylinderPullback g N.coordinate_map z v w)
              (chartAt E₂ q) y a b) (0, s)‖ ≤ C * rho := by
  obtain ⟨C, hC, hbound⟩ := terminalCurvature_exists_neck_chart_error_constant_uniform m hD
  exact ⟨C, hC, hbound M X⟩

end PoincareConjecture.M47
