import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckMetric
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

theorem centeredCylinderMetric_smul (B : RoundCylinderTwoTensor)
    (c : ℝ) (q : UnitTwoSphere) (s : ℝ) (p : E) :
    centeredCylinderMetric (fun z v w => c * B z v w) q s p =
      c • centeredCylinderMetric B q s p := by
  apply euclideanThree_bilinear_ext
  intro a b
  simp only [centeredCylinderMetric, centeredCylinderBilinear_basis,
    smul_apply, smul_eq_mul, roundCylinderTensorCoefficient]

theorem centeredCylinderMetric_congr {ε : ℝ} {B₁ B₀ : RoundCylinderTwoTensor}
    (hB : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v w, B₁ z v w = B₀ z v w)
    (q : UnitTwoSphere) (s : ℝ) {p : E}
    (hp : cylinderHeightCovector p + s ∈ Ioo (-ε⁻¹) ε⁻¹) :
    centeredCylinderMetric B₁ q s p = centeredCylinderMetric B₀ q s p := by
  apply euclideanThree_bilinear_ext
  intro a b
  simp only [centeredCylinderMetric, centeredCylinderBilinear_basis,
    roundCylinderTensorCoefficient]
  exact hB _ hp _ _

theorem centeredCylinderMetric_pullback
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn IC (𝓡 3) ∞ f (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (q : UnitTwoSphere) (s : ℝ) {p : E}
    (hp : cylinderHeightCovector p + s ∈ Ioo (-ε⁻¹) ε⁻¹) :
    centeredCylinderMetric (roundCylinderPullback g f) q s p =
      g.pullbackCoefficients (f ∘ centeredCylinderLift q s) p := by
  have hfd := (hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show centeredCylinderLift q s p ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ from
      ⟨mem_univ _, hp⟩))).mdifferentiableAt (by simp)
  have hcd := (centeredCylinderLift_contMDiff q s p).mdifferentiableAt (by simp)
  apply euclideanThree_bilinear_ext
  intro a b
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    exact Prod.ext (add_zero _) rfl
  rw [hcoord]
  change _ = g.inner (f (centeredCylinderLift q s p))
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ centeredCylinderLift q s) p
      (EuclideanSpace.basisFun (Fin 3) ℝ a))
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ centeredCylinderLift q s) p
      (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [mfderiv_comp p hfd hcd]
  change _ = g.inner (f (centeredCylinderLift q s p))
    (mfderiv IC (𝓡 3) f (centeredCylinderLift q s p)
      (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p (EuclideanSpace.basisFun (Fin 3) ℝ a)))
    (mfderiv IC (𝓡 3) f (centeredCylinderLift q s p)
      (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p (EuclideanSpace.basisFun (Fin 3) ℝ b)))
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv]
  have hP (i : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      (roundCylinderCoordinateBasis i).1 := congrArg Prod.fst (cylinderEuclideanEquiv_basis i)
  simp only [hP, cylinderHeightCovector_basis]
  rfl

private noncomputable def centeredCoefficientEvaluation (a b : Fin 3) : Bilin →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ a))

private theorem centeredCoefficientEvaluation_norm_le (a b : Fin 3) :
    ‖centeredCoefficientEvaluation a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro B
  simpa only [centeredCoefficientEvaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, OrthonormalBasis.norm_eq_one, mul_one, one_mul] using
    B.le_opNorm₂ (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)

theorem cylinder_coefficient_jet_le_centered_metric_jet
    (B₁ B₀ : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s : ℝ)
    (hF : ContDiffAt ℝ ∞ (fun p => centeredCylinderMetric B₁ q s p -
      centeredCylinderMetric B₀ q s p) 0) (j : ℕ) (a b : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B₁ (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient B₀ (chartAt E₂ q) y a b) (0, s)‖ ≤
      ‖iteratedFDeriv ℝ j (fun p => centeredCylinderMetric B₁ q s p -
          centeredCylinderMetric B₀ q s p) 0‖ *
        ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j := by
  let D : E → Bilin := fun p => centeredCylinderMetric B₁ q s p - centeredCylinderMetric B₀ q s p
  let L := centeredCoefficientEvaluation a b
  let c : RoundCylinderCoordinates := (0, s)
  have heq : (fun y => roundCylinderTensorCoefficient B₁ (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient B₀ (chartAt E₂ q) y a b) =
      fun y => (L ∘ D ∘ cylinderEuclideanEquiv.symm) (y - c) := by
    funext y
    change _ = (centeredCylinderMetric B₁ q s (cylinderEuclideanEquiv.symm (y - c)) -
      centeredCylinderMetric B₀ q s (cylinderEuclideanEquiv.symm (y - c)))
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
    simp only [sub_apply, centeredCylinderMetric, centeredCylinderBilinear_basis,
      ContinuousLinearEquiv.apply_symm_apply, c, sub_add_cancel]
  rw [heq, iteratedFDeriv_comp_sub, sub_self]
  have hlinear := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    cylinderEuclideanEquiv.symm (L ∘ D) j 0
  have heval := L.norm_iteratedFDeriv_comp_left hF (by exact_mod_cast le_top : (j : ℕ∞ω) ≤ ∞)
  have heval' : ‖iteratedFDeriv ℝ j (L ∘ D) 0‖ ≤ ‖iteratedFDeriv ℝ j D 0‖ :=
    heval.trans ((mul_le_mul_of_nonneg_right (centeredCoefficientEvaluation_norm_le a b)
      (norm_nonneg _)).trans_eq (one_mul _))
  apply hlinear.trans
  simpa only [map_zero] using mul_le_mul_of_nonneg_right heval'
    (pow_nonneg (norm_nonneg _) j)

theorem exists_cylinder_coefficient_jet_constant (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B₁ B₀ : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s : ℝ),
      ContDiffAt ℝ ∞ (fun p => centeredCylinderMetric B₁ q s p -
        centeredCylinderMetric B₀ q s p) 0 →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun p => centeredCylinderMetric B₁ q s p -
        centeredCylinderMetric B₀ q s p) 0‖ ≤ A) →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient B₁ (chartAt E₂ q) y a b -
            roundCylinderTensorCoefficient B₀ (chartAt E₂ q) y a b) (0, s)‖ ≤ C * A := by
  let C := max 1 ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C ^ m, pow_pos (lt_of_lt_of_le zero_lt_one hC) m, ?_⟩
  intro B₁ B₀ q s hF A hA hj j hjm a b
  have hp : ‖cylinderEuclideanEquiv.symm.toContinuousLinearMap‖ ^ j ≤ C ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ hC hjm)
  exact (cylinder_coefficient_jet_le_centered_metric_jet B₁ B₀ q s hF j a b).trans
    ((mul_le_mul (hj j hjm) hp (pow_nonneg (norm_nonneg _) j) hA).trans_eq (mul_comm A _))

end PoincareConjecture.MetricSurgery
