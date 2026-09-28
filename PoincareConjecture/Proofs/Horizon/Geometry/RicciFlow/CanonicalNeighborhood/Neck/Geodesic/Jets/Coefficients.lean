import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Centered
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

theorem cylinderCoordinate_decomposition (v : RoundCylinderCoordinates) :
    v = v.1 0 • roundCylinderCoordinateBasis 0 +
      v.1 1 • roundCylinderCoordinateBasis 1 + v.2 • roundCylinderCoordinateBasis 2 := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
  · simp [roundCylinderCoordinateBasis]

theorem norm_le_of_cylinder_basis_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : RoundCylinderCoordinates →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i, ‖A (roundCylinderCoordinateBasis i)‖ ≤ C) : ‖A‖ ≤ 3 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h₀ : |v.1 0| ≤ ‖v‖ := by
    exact (show |v.1 0| ≤ ‖v.1‖ from PiLp.norm_apply_le v.1 0).trans (norm_fst_le v)
  have h₁ : |v.1 1| ≤ ‖v‖ := by
    exact (show |v.1 1| ≤ ‖v.1‖ from PiLp.norm_apply_le v.1 1).trans (norm_fst_le v)
  have h₂ : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  calc
    ‖A v‖ = ‖v.1 0 • A (roundCylinderCoordinateBasis 0) +
        v.1 1 • A (roundCylinderCoordinateBasis 1) + v.2 • A (roundCylinderCoordinateBasis 2)‖ := by
      conv_lhs => rw [cylinderCoordinate_decomposition v]
      rw [map_add, map_add, map_smul, map_smul, map_smul]
    _ ≤ ‖v.1 0 • A (roundCylinderCoordinateBasis 0)‖ +
        ‖v.1 1 • A (roundCylinderCoordinateBasis 1)‖ +
        ‖v.2 • A (roundCylinderCoordinateBasis 2)‖ := norm_add₃_le
    _ ≤ ‖v‖ * C + ‖v‖ * C + ‖v‖ * C := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (add_le_add
        (mul_le_mul h₀ (hA 0) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul h₁ (hA 1) (norm_nonneg _) (norm_nonneg _)))
        (mul_le_mul h₂ (hA 2) (norm_nonneg _) (norm_nonneg _))
    _ = (3 * C) * ‖v‖ := by ring

theorem fderiv_bilinear_evaluation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (u : E) (v w : F) :
    fderiv ℝ (fun y => B y v w) x u = fderiv ℝ B x u v w := by
  have h := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)).fderiv
  simpa only [ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using congrArg (fun A => A u) h

theorem norm_fderiv_bilinearComp_linear_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (T : F →L[ℝ] E) {x : F}
    (hB : DifferentiableAt ℝ B (T x)) :
    ‖fderiv ℝ (fun y => (B (T y)).bilinearComp T T) x‖ ≤
      ‖fderiv ℝ B (T x)‖ * ‖T‖ ^ 3 := by
  let A := fun y => (B (T y)).bilinearComp T T
  have hA : DifferentiableAt ℝ A x := by
    have h₁ := (hB.comp x T.differentiableAt).clm_comp (differentiableAt_const T)
    have h₂ := (ContinuousLinearMap.flipₗᵢ ℝ F E ℝ).toLinearIsometry.toContinuousLinearMap.differentiableAt.comp x h₁
    have h₃ := h₂.clm_comp (differentiableAt_const T)
    exact (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).toLinearIsometry.toContinuousLinearMap.differentiableAt.comp x h₃
  have heq (u v w : F) : fderiv ℝ A x u v w =
      fderiv ℝ B (T x) (T u) (T v) (T w) := by
    rw [← fderiv_bilinear_evaluation hA]
    change fderiv ℝ ((fun y => B y (T v) (T w)) ∘ T) x u = _
    rw [fderiv_comp x
      ((hB.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _))
      T.differentiableAt, T.fderiv]
    exact fderiv_bilinear_evaluation hB (T u) (T v) (T w)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ B (T x) (T u)‖ * ‖T v‖ * ‖T w‖ :=
      (fderiv ℝ B (T x) (T u)).le_opNorm₂ _ _
    _ ≤ ‖fderiv ℝ B (T x)‖ * ‖T u‖ * ‖T v‖ * ‖T w‖ := by
      gcongr
      exact (fderiv ℝ B (T x)).le_opNorm _
    _ ≤ ‖fderiv ℝ B (T x)‖ * (‖T‖ * ‖u‖) * (‖T‖ * ‖v‖) * (‖T‖ * ‖w‖) := by
      gcongr <;> exact T.le_opNorm _
    _ = (‖fderiv ℝ B (T x)‖ * ‖T‖ ^ 3 * ‖u‖) * ‖v‖ * ‖w‖ := by ring

namespace EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

def centeredParametrization (N : EpsilonNeck g) (q : UnitTwoSphere)
    (y : RoundCylinderCoordinates) : M :=
  N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)

def normalizedCenteredCoefficients (N : EpsilonNeck g) (q : UnitTwoSphere)
    (y : RoundCylinderCoordinates) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
  N.scale⁻¹ ^ 2 • g.parametrizedCoefficients (N.centeredParametrization q) y

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem centeredParametrization_contMDiffAt (N : EpsilonNeck g) (q : UnitTwoSphere)
    {y : RoundCylinderCoordinates} (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
      (N.centeredParametrization q) y := by
  exact (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hy⟩)).comp y
      (cylinderChart_symm_smooth q y)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem normalizedCenteredCoefficients_contDiffAt
    (N : EpsilonNeck g) (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (N.normalizedCenteredCoefficients q) y :=
  (g.contDiffAt_parametrizedCoefficients
    (N.centeredParametrization_contMDiffAt q hy)).const_smul _

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem normalizedCenteredCoefficients_basis_eventuallyEq
    (N : EpsilonNeck g) (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i j : Fin 3) :
    (fun p => roundCylinderTensorCoefficient N.normalized_pullback
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) =ᶠ[𝓝 y]
    (fun p => N.normalizedCenteredCoefficients q p
      (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) := by
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds hy)] with p hp
  change N.scale⁻¹ ^ 2 * roundCylinderTensorCoefficient
      (roundCylinderPullback g N.coordinate_map)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j = _
  have hp' : ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2) ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hp⟩
  rw [roundCylinderTensorCoefficient_pullback_eq g q N.coordinate_map p
    ((N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp')).mdifferentiableAt (by simp))]
  rfl



theorem norm_fderiv_normalizedCenteredCoefficients_le
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ‖fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)‖ ≤ 216 * N.epsilon := by
  have hε := N.epsilon_pos
  have hB := (N.normalizedCenteredCoefficients_contDiffAt q (y := (0, s)) hs).differentiableAt (by simp)
  have hcomponent (i j k : Fin 3) :
      ‖fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)
        (roundCylinderCoordinateBasis k)‖ ≤ 8 * N.epsilon := by
    have h := N.abs_normalized_pullback_coefficient_derivative_center_le q hs i j k
    rw [(N.normalizedCenteredCoefficients_basis_eventuallyEq q (y := (0, s)) hs j k).fderiv_eq,
      fderiv_bilinear_evaluation hB] at h
    exact h
  have h₁ (i j : Fin 3) :
      ‖fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)‖ ≤
        24 * N.epsilon := by
    convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 8 * N.epsilon from by
      positivity) (hcomponent i j) using 1
    ring
  have h₂ (i : Fin 3) :
      ‖fderiv ℝ (N.normalizedCenteredCoefficients q) (0, s)
        (roundCylinderCoordinateBasis i)‖ ≤ 72 * N.epsilon := by
    convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 24 * N.epsilon from by
      positivity) (h₁ i) using 1
    ring
  convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 72 * N.epsilon from by
    positivity) h₂ using 1
  ring

end EpsilonNeck

end PoincareConjecture
