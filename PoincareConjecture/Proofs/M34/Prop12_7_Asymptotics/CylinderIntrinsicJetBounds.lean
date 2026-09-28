import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderCovariantJetBounds
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderJetErrorBound
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderParametrizedJets
import PoincareConjecture.Proofs.M34.Mathlib.LinearPostcomposeGermJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem exists_roundCylinderJetErrorSquared_bound_on_Icc {T : ℝ} (hT : T < 1)
    {J : Set ℝ} (hJ : IsCompact J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T,
      ∀ (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace), z.2 ∈ J →
      ∀ A : ℝ, 0 ≤ A →
      (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ z.1) y a b -
          roundCylinderGram u (chartAt E₂ z.1) y a b) (0, z.2)) →
      (∀ j ≤ m, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ z.1) y a b -
          roundCylinderGram u (chartAt E₂ z.1) y a b) (0, z.2)‖ ≤ A) →
      roundCylinderJetErrorSquared u B m z ≤ C * A ^ 2 := by
  obtain ⟨D, hD, hb⟩ := exists_roundCylinder_covariant_component_bound hT
    ((isCompact_singleton (x := (0 : E₂))).prod hJ) m
  let M : ℝ := max 1 ((2 * (1 - T))⁻¹)
  have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  let W : ℝ := ∑ k ∈ Finset.range (m + 1), ((3 : ℝ) ^ (2 + k)) ^ 2 * M ^ (2 + k)
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg hM _)
  refine ⟨W * D ^ 2, mul_nonneg hW (sq_nonneg _), ?_⟩
  intro u hu B z hz A hA hs hjet
  have h := roundCylinderJetErrorSquared_le (B := B) (order := m) (z := z)
    (δ := D * A) hM
    (roundCylinderGram_chart_center_inv_le hT hu z.1 z.2)
    (fun k hk a => ?_)
  · exact h.trans_eq (by dsimp [W]; rw [← Finset.sum_mul]; ring)
  · simpa only [sphere_chart_center_zero] using
      hb u hu z.1 B (0, z.2) ⟨rfl, hz⟩ A hA hs hjet k hk a

private noncomputable def parameterCoefficientEvaluation (a b : Fin 3) :
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis b)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis a))

private theorem norm_parameterCoordinateBasis (i : Fin 3) :
    ‖roundCylinderCoordinateBasis i‖ = 1 := by
  fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]

private theorem norm_parameterCoefficientEvaluation_le (a b : Fin 3) :
    ‖parameterCoefficientEvaluation a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa only [parameterCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, norm_parameterCoordinateBasis,
    mul_one, one_mul] using
    B.le_opNorm₂ (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)

private theorem parameter_coefficient_error_eventuallyEq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U)
    (u : ℝ) (q : UnitTwoSphere) {x : RoundCylinderCoordinates}
    (hx : ((chartAt E₂ q).symm x.1, x.2) ∈ U) (a b : Fin 3) :
    (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g f)
      (chartAt E₂ q) y a b - roundCylinderGram u (chartAt E₂ q) y a b) =ᶠ[𝓝 x]
    (parameterCoefficientEvaluation a b) ∘ (fun y => g.parametrizedCoefficients
      (fun p => f ((chartAt E₂ q).symm p.1, p.2)) y -
        evolvingRoundCylinderModelCoefficients u y) := by
  have hnear := (cylinderChart_symm_smooth q).continuous.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hx)
  filter_upwards [hnear] with y hy
  have heq := roundCylinderTensorCoefficient_pullback_eq g q f y
    ((hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) a b
  rw [heq, roundCylinderGram_eq_stereographic_formula]
  simp only [parameterCoefficientEvaluation, Function.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    sub_apply, RiemannianMetric.parametrizedCoefficients_apply,
    evolvingRoundCylinderModelCoefficients_apply]

private theorem exists_parameter_coefficient_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
        {U : Set RoundCylinderSpace}, IsOpen U →
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U →
        ∀ (z : RoundCylinderSpace), z ∈ U →
        ∀ A : ℝ, 0 ≤ A →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => g.parametrizedCoefficients
          (fun p => f ((chartAt E₂ z.1).symm p.1, p.2)) y -
            evolvingRoundCylinderModelCoefficients u y) (0, z.2)‖ ≤ A) →
        (∀ a b : Fin 3, ContDiffAt ℝ ∞ (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback g f) (chartAt E₂ z.1) y a b -
            roundCylinderGram u (chartAt E₂ z.1) y a b) (0, z.2)) ∧
        (∀ j ≤ m, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback g f) (chartAt E₂ z.1) y a b -
            roundCylinderGram u (chartAt E₂ z.1) y a b) (0, z.2)‖ ≤ C * A) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro u M _ _ _ g f U hU hf z hz A hA hjet
  let x : RoundCylinderCoordinates := (0, z.2)
  have hx : ((chartAt E₂ z.1).symm x.1, x.2) ∈ U := by
    simpa only [x, sphere_chart_symm_zero] using hz
  let D : RoundCylinderCoordinates → RoundCylinderCoordinates →L[ℝ]
      RoundCylinderCoordinates →L[ℝ] ℝ := fun y => g.parametrizedCoefficients
    (fun p => f ((chartAt E₂ z.1).symm p.1, p.2)) y -
      evolvingRoundCylinderModelCoefficients u y
  have hmap := (hf.contMDiffAt (hU.mem_nhds hx)).comp x (cylinderChart_symm_smooth z.1 x)
  have hDs : ContDiffAt ℝ ∞ D x :=
    (g.contDiffAt_parametrizedCoefficients hmap).sub
      (contDiff_evolvingRoundCylinderModelCoefficients u).contDiffAt
  have hevalJets (a b : Fin 3) := Poincare.Analysis.Calculus.clm_comp_germ_jet_bound
    (parameterCoefficientEvaluation a b) hDs
    (parameter_coefficient_error_eventuallyEq g hU hf u z.1 hx a b)
    m zero_le_one (norm_parameterCoefficientEvaluation_le a b) hjet
  exact ⟨fun a b => (hevalJets a b).1, fun j hj a b => (hevalJets a b).2 j hj⟩

theorem exists_roundCylinderJetErrorSquared_bound_of_parametrizedJets_on_Icc
    {T : ℝ} (hT : T < 1) {J : Set ℝ} (hJ : IsCompact J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T,
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
        {U : Set RoundCylinderSpace}, IsOpen U →
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U →
        ∀ (z : RoundCylinderSpace), z ∈ U → z.2 ∈ J →
        ∀ A : ℝ, 0 ≤ A →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun y => g.parametrizedCoefficients
          (fun p => f ((chartAt E₂ z.1).symm p.1, p.2)) y -
            evolvingRoundCylinderModelCoefficients u y) (0, z.2)‖ ≤ A) →
        roundCylinderJetErrorSquared u (roundCylinderPullback g f) m z ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_roundCylinderJetErrorSquared_bound_on_Icc hT hJ m
  obtain ⟨D, hD, hparam⟩ := exists_parameter_coefficient_jet_bound m
  refine ⟨C * D ^ 2, mul_nonneg hC (sq_nonneg _), ?_⟩
  intro u hu M _ _ _ g f U hU hf z hz hzJ A hA hjet
  have hjets := hparam u g hU hf z hz A hA hjet
  have hb := hbound u hu (roundCylinderPullback g f) z hzJ (D * A)
    (mul_nonneg hD hA) hjets.1 hjets.2
  exact hb.trans_eq (by ring)

end PoincareConjecture.M34
