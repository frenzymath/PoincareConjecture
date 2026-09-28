import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.FiniteJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

theorem norm_roundCylinderCoordinateBasis (i : Fin 3) :
    ‖roundCylinderCoordinateBasis i‖ = 1 := by
  fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]

private noncomputable def cylinderCoefficientEvaluation (a b : Fin 3) :
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis b)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis a))

private theorem norm_cylinderCoefficientEvaluation_le (a b : Fin 3) :
    ‖cylinderCoefficientEvaluation a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro B
  simpa only [cylinderCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, norm_roundCylinderCoordinateBasis, mul_one, one_mul]
    using B.le_opNorm₂ (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)

private theorem cylinder_coefficient_error_eventuallyEq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U)
    (s : ℝ) (q : UnitTwoSphere) {x : RoundCylinderCoordinates}
    (hx : ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2) ∈ U)
    (a b : Fin 3) :
    (fun y => roundCylinderTensorCoefficient
      (fun z v w => s * roundCylinderPullback g f z v w)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) =ᶠ[𝓝 x]
    (cylinderCoefficientEvaluation a b) ∘
      (fun y => s • g.parametrizedCoefficients
        (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) y -
          roundCylinderModelCoefficients y) := by
  have hnear := (cylinderChart_symm_smooth q).continuous.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hx)
  filter_upwards [hnear] with y hy
  have heq := roundCylinderTensorCoefficient_pullback_eq g q f y
    ((hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) a b
  change s * roundCylinderTensorCoefficient (roundCylinderPullback g f)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b - _ = _
  rw [heq, roundCylinderGram_eq_stereographic_formula]
  simp only [cylinderCoefficientEvaluation, Function.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    sub_apply, smul_apply, smul_eq_mul, RiemannianMetric.parametrizedCoefficients_apply,
    roundCylinderModelCoefficients_apply]
  ring

theorem exists_roundCylinderJetErrorSquared_bound_of_parametrizedJets
    {J : Set ℝ} (hJ : IsCompact J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
        {U : Set RoundCylinderSpace}, IsOpen U →
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U →
        ∀ (s : ℝ) (z : RoundCylinderSpace), z ∈ U → z.2 ∈ J →
        ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ m →
          ‖iteratedFDeriv ℝ j (fun y =>
            s • g.parametrizedCoefficients
              (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)) y -
                roundCylinderModelCoefficients y) (0, z.2)‖ ≤ A) →
        roundCylinderJetErrorSquared 0
          (fun y v w => s * roundCylinderPullback g f y v w) m z ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_roundCylinderJetErrorSquared_bound hJ m
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g f U hU hf s z hz hzJ A hA hjet
  let x : RoundCylinderCoordinates := (0, z.2)
  have hx : ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm x.1, x.2) ∈ U := by
    simpa only [x, sphere_chart_symm_zero] using hz
  let D : RoundCylinderCoordinates → RoundCylinderCoordinates →L[ℝ]
      RoundCylinderCoordinates →L[ℝ] ℝ := fun y =>
    s • g.parametrizedCoefficients
      (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)) y -
        roundCylinderModelCoefficients y
  have hmap := (hf.contMDiffAt (hU.mem_nhds hx)).comp x
    (cylinderChart_symm_smooth z.1 x)
  have hD : ContDiffAt ℝ ∞ D x :=
    ((g.contDiffAt_parametrizedCoefficients hmap).const_smul s).sub
      contDiff_roundCylinderModelCoefficients.contDiffAt
  apply hbound _ z hzJ A hA
  · intro a b
    exact ((cylinderCoefficientEvaluation a b).contDiff.contDiffAt.comp x hD).congr_of_eventuallyEq
      (cylinder_coefficient_error_eventuallyEq g hU hf s z.1 hx a b)
  · intro j hj a b
    have heq := ((cylinder_coefficient_error_eventuallyEq g hU hf s z.1 hx a b).iteratedFDeriv ℝ j).self_of_nhds
    rw [heq]
    have h := (cylinderCoefficientEvaluation a b).norm_iteratedFDeriv_comp_left
      hD (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
    exact h.trans ((mul_le_mul_of_nonneg_right (norm_cylinderCoefficientEvaluation_le a b)
      (norm_nonneg _)).trans (by simpa only [one_mul] using hjet j hj))

end PoincareConjecture
