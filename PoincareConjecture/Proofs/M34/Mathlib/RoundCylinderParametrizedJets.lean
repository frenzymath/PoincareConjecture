import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderFiniteJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model
import Mathlib.Tactic.FinCases











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.M34

private noncomputable def cylinderCoefficientEvaluation (a b : Fin 3) :
    (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis b)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis a))

private theorem norm_roundCylinderCoordinateBasis_eq_one (i : Fin 3) :
    ‖roundCylinderCoordinateBasis i‖ = 1 := by
  fin_cases i <;> simp [roundCylinderCoordinateBasis, Prod.norm_def]

private theorem norm_cylinderCoefficientEvaluation_le (a b : Fin 3) :
    ‖cylinderCoefficientEvaluation a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro B
  simpa only [cylinderCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, norm_roundCylinderCoordinateBasis_eq_one,
    mul_one, one_mul] using
    B.le_opNorm₂ (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)



noncomputable def evolvingRoundCylinderModelCoefficients (u : ℝ)
    (p : RoundCylinderCoordinates) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ := by
  let B : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
    ContinuousLinearMap.bilinearComp (σ₁₃' := RingHom.id ℝ)
      (innerSL ℝ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  exact (2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2)) • B +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)

@[simp] theorem evolvingRoundCylinderModelCoefficients_apply
    (u : ℝ) (p v w : RoundCylinderCoordinates) :
    evolvingRoundCylinderModelCoefficients u p v w =
      2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2) *
        inner ℝ v.1 w.1 + v.2 * w.2 :=
  rfl

theorem contDiff_evolvingRoundCylinderModelCoefficients (u : ℝ) :
    ContDiff ℝ ∞ (evolvingRoundCylinderModelCoefficients u) := by
  let : IsBoundedSMul ℝ
      (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)
  have hs : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2)) :=
    contDiff_const.mul (contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 2)
      (fun p => by positivity))
  exact (hs.smul contDiff_const).add contDiff_const

private theorem cylinder_coefficient_error_eventuallyEq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U)
    (u : ℝ) (q : UnitTwoSphere) {x : RoundCylinderCoordinates}
    (hx : ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2) ∈ U)
    (a b : Fin 3) :
    (fun y => roundCylinderTensorCoefficient
      (roundCylinderPullback g f)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b -
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) =ᶠ[𝓝 x]
    (cylinderCoefficientEvaluation a b) ∘
      (fun y => g.parametrizedCoefficients
        (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) y -
          evolvingRoundCylinderModelCoefficients u y) := by
  have hnear := (cylinderChart_symm_smooth q).continuous.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hx)
  filter_upwards [hnear] with y hy
  have heq := roundCylinderTensorCoefficient_pullback_eq g q f y
    ((hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)) a b
  rw [heq, roundCylinderGram_eq_stereographic_formula]
  simp only [cylinderCoefficientEvaluation, Function.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    sub_apply, RiemannianMetric.parametrizedCoefficients_apply,
    evolvingRoundCylinderModelCoefficients_apply]



theorem exists_evolvingRoundCylinderJetErrorSquared_bound_of_parametrizedJets
    {u : ℝ} (hu : u < 1) {J : Set ℝ} (hJ : IsCompact J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
        {U : Set RoundCylinderSpace}, IsOpen U →
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U →
        ∀ (z : RoundCylinderSpace), z ∈ U → z.2 ∈ J →
        ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ m →
          ‖iteratedFDeriv ℝ j (fun y =>
            g.parametrizedCoefficients
              (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)) y -
                evolvingRoundCylinderModelCoefficients u y) (0, z.2)‖ ≤ A) →
        roundCylinderJetErrorSquared u (roundCylinderPullback g f) m z ≤ C * A ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_evolvingRoundCylinderJetErrorSquared_bound hu hJ m
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g f U hU hf z hz hzJ A hA hjet
  let x : RoundCylinderCoordinates := (0, z.2)
  have hx : ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm x.1, x.2) ∈ U := by
    simpa only [x, sphere_chart_symm_zero] using hz
  let D : RoundCylinderCoordinates → RoundCylinderCoordinates →L[ℝ]
      RoundCylinderCoordinates →L[ℝ] ℝ := fun y =>
    g.parametrizedCoefficients
      (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)) y -
        evolvingRoundCylinderModelCoefficients u y
  have hmap := (hf.contMDiffAt (hU.mem_nhds hx)).comp x
    (cylinderChart_symm_smooth z.1 x)
  have hD : ContDiffAt ℝ ∞ D x :=
    (g.contDiffAt_parametrizedCoefficients hmap).sub
      (contDiff_evolvingRoundCylinderModelCoefficients u).contDiffAt
  apply hbound _ z hzJ A hA
  · intro a b
    exact ((cylinderCoefficientEvaluation a b).contDiff.contDiffAt.comp x hD).congr_of_eventuallyEq
      (cylinder_coefficient_error_eventuallyEq g hU hf u z.1 hx a b)
  · intro j hj a b
    have heq :=
      (cylinder_coefficient_error_eventuallyEq g hU hf u z.1 hx a b).iteratedFDeriv ℝ j
    rw [heq.self_of_nhds]
    have h := (cylinderCoefficientEvaluation a b).norm_iteratedFDeriv_comp_left
      hD (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (norm_cylinderCoefficientEvaluation_le a b) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hjet j hj))

end PoincareConjecture.M34
