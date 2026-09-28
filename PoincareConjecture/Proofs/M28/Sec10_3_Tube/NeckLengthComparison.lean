import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.TensorNorms
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M28.NeckLengthComparison

open NeckAnalysis

private theorem sum_two_indices (f : Fin 3 → Fin 3 → ℝ) :
    (∑ a : Fin 2 → Fin 3, f (a 0) (a 1)) = ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ p : Fin 3 × Fin 3, f p.1 p.2 :=
      (finTwoArrowEquiv (Fin 3)).sum_comp (fun p => f p.1 p.2)
    _ = _ := Fintype.sum_prod_type _

private theorem weighted_quadratic_le
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 < d i) (T : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hT : (∑ i, ∑ j, (d i)⁻¹ * (d j)⁻¹ * (T i j) ^ 2) ≤ epsilon ^ 2) :
    |∑ i, ∑ j, T i j * x i * x j| ≤ epsilon * ∑ i, d i * (x i) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin 3 × Fin 3))
    (r := fun p => T p.1 p.2 * x p.1 * x p.2)
    (f := fun p => (d p.1)⁻¹ * (d p.2)⁻¹ * (T p.1 p.2) ^ 2)
    (g := fun p => d p.1 * d p.2 * (x p.1 * x p.2) ^ 2)
    (fun p _ => mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (hd p.1).le) (inv_nonneg.mpr (hd p.2).le))
      (sq_nonneg _))
    (fun p _ => mul_nonneg (mul_nonneg (hd p.1).le (hd p.2).le) (sq_nonneg _))
    (fun p _ => le_of_eq (by
      field_simp [ne_of_gt (hd p.1), ne_of_gt (hd p.2)]))
  have hfactor :
      (∑ p : Fin 3 × Fin 3, d p.1 * d p.2 * (x p.1 * x p.2) ^ 2) =
        (∑ i, d i * (x i) ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor] at hcs
  simp only [Fintype.sum_prod_type] at hcs
  have hnonneg : 0 ≤ ∑ i, d i * (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hepsilon hnonneg)).mp
  rw [sq_abs, mul_pow]
  exact hcs.trans (mul_le_mul_of_nonneg_right hT (sq_nonneg _))

set_option backward.isDefEq.respectTransparency false in
private theorem sphere_chart_symm_mfderiv (q : UnitTwoSphere) :
    mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 2) (x := q)
  have hr : Set.range (𝓡 2) = Set.univ := by ext x; simp
  rw [hr, mfderivWithin_univ] at h
  convert! h using 1

set_option backward.isDefEq.respectTransparency false in

theorem sphere_inclusion_inner (q : UnitTwoSphere)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q w) =
        inner ℝ v w := by
  have h := sphere_chart_inverse_inner q v w
  dsimp only at h
  rw [(chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv (mem_chart_source _ q),
    sphere_chart_symm_mfderiv] at h
  simpa only [ContinuousLinearMap.id_apply] using! h

private theorem tensor_coefficient_center (B : RoundCylinderTwoTensor)
    (z : RoundCylinderSpace) (a b : Fin 3) :
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a b =
        B z (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) := by
  unfold roundCylinderTensorCoefficient
  dsimp only
  rw [(chartAt (EuclideanSpace ℝ (Fin 2)) z.1).left_inv (mem_chart_source _ z.1),
    sphere_chart_symm_mfderiv]
  rfl

theorem roundCylinderMetric_self_eq (z : RoundCylinderSpace)
    (v : RoundCylinderCoordinates) :
    RoundCylinderMetric z v v = 2 * ‖v.1‖ ^ 2 + v.2 ^ 2 := by
  dsimp only [RoundCylinderMetric, EvolvingRoundCylinderMetric]
  rw [sphere_inclusion_inner, real_inner_self_eq_norm_sq]
  ring

private noncomputable def coordinateComponents (v : RoundCylinderCoordinates) : Fin 3 → ℝ :=
  ![v.1 0, v.1 1, v.2]

private theorem coordinateComponents_sum (v : RoundCylinderCoordinates) :
    (∑ i : Fin 3, coordinateComponents v i • roundCylinderCoordinateBasis i) = v := by
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [coordinateComponents, roundCylinderCoordinateBasis, Fin.sum_univ_three,
        EuclideanSpace.basisFun_apply]
  · simp [coordinateComponents, roundCylinderCoordinateBasis, Fin.sum_univ_three]

private theorem bilinear_quadratic_sum
    (B : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)
    (v : RoundCylinderCoordinates) :
    B v v = ∑ i, ∑ j, B (roundCylinderCoordinateBasis i)
      (roundCylinderCoordinateBasis j) * coordinateComponents v i *
        coordinateComponents v j := by
  calc
    B v v = B (∑ i, coordinateComponents v i • roundCylinderCoordinateBasis i)
        (∑ j, coordinateComponents v j • roundCylinderCoordinateBasis j) := by
      simp only [coordinateComponents_sum]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private noncomputable def modelForm :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
  2 • (innerSL ℝ).bilinearComp (ContinuousLinearMap.fst ℝ _ _)
    (ContinuousLinearMap.fst ℝ _ _) +
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ _ _)
    (ContinuousLinearMap.snd ℝ _ _)

private theorem modelForm_apply (z : RoundCylinderSpace)
    (v w : RoundCylinderCoordinates) : modelForm v w = RoundCylinderMetric z v w := by
  simp [modelForm, RoundCylinderMetric, EvolvingRoundCylinderMetric,
    sphere_inclusion_inner, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, mul_comm]

private theorem modelForm_diagonal (z : RoundCylinderSpace)
    (v : RoundCylinderCoordinates) :
    (∑ i, cylinderGramDiagonal 0 i * (coordinateComponents v i) ^ 2) =
      RoundCylinderMetric z v v := by
  rw [roundCylinderMetric_self_eq, EuclideanSpace.real_norm_sq_eq]
  simp [coordinateComponents, cylinderGramDiagonal, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

private noncomputable def cylinderTangentFrame (z : RoundCylinderSpace) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderTangent z :=
  (trivializationAt RoundCylinderCoordinates
    (TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ))) z).symmL ℝ z

set_option backward.isDefEq.respectTransparency false in
private theorem cylinderTangentFrame_apply (z : RoundCylinderSpace)
    (v : RoundCylinderCoordinates) : cylinderTangentFrame z v = v := by
  unfold cylinderTangentFrame
  rw [TangentBundle.symmL_trivializationAt (mem_chart_source _ z),
    mfderivWithin_range_extChartAt_symm]
  rfl

end PoincareConjecture.Proofs.M28.NeckLengthComparison

namespace PoincareConjecture.EpsilonNeck

open Proofs.M28.NeckLengthComparison Proofs.M28.NeckAnalysis

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalized_metric_quadratic_bounds (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderCoordinates) :
    (1 - N.epsilon) * RoundCylinderMetric z v v ≤
        N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ∧
      N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v ≤
        (1 + N.epsilon) * RoundCylinderMetric z v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : RoundCylinderTwoTensor := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w
  let D : RoundCylinderCoordinates →L[ℝ] TangentSpace (𝓡 3) (N.coordinate_map z) :=
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z).comp
      (cylinderTangentFrame z)
  let E : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
    N.scale⁻¹ ^ 2 • (g.inner (N.coordinate_map z)).bilinearComp D D - modelForm
  have hE (v w : RoundCylinderCoordinates) : E v w = B z v w - RoundCylinderMetric z v w := by
    simp [E, B, D, roundCylinderPullback, modelForm_apply z, cylinderTangentFrame_apply]
  obtain ⟨bound, hbound, hclose⟩ := N.metric_comparison.close.2
  have hzero : roundCylinderJetErrorSquared 0 B 0 z ≤ N.epsilon ^ 2 :=
    ((roundCylinderJetErrorSquared_mono_order (by norm_num) B (Nat.zero_le _) z).trans
      (hclose z hz)).trans hbound.le
  have hcoeff (a : Fin 2 → Fin 3) :
      roundCylinderIteratedDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1 z.1, z.2) a =
          E (roundCylinderCoordinateBasis (a 0)) (roundCylinderCoordinateBasis (a 1)) := by
    simp only [roundCylinderIteratedDerivative, roundCylinderGram,
      tensor_coefficient_center, hE, RoundCylinderMetric]
  have hsum : (∑ i, ∑ j, (cylinderGramDiagonal 0 i)⁻¹ *
      (cylinderGramDiagonal 0 j)⁻¹ *
      (E (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2) ≤
        N.epsilon ^ 2 := by
    have hsum0 : (∑ a : Fin 2 → Fin 3, cylinderTensorWeight 0 a *
        (E (roundCylinderCoordinateBasis (a 0)) (roundCylinderCoordinateBasis (a 1))) ^ 2) ≤
          N.epsilon ^ 2 := by
      simpa only [roundCylinderJetErrorSquared, Nat.zero_add, Nat.add_zero,
        Finset.sum_range_one,
        roundCylinderTensorNormSquared_eq_sum (by norm_num : (0 : ℝ) < 1),
        hcoeff] using hzero
    let F : Fin 3 → Fin 3 → ℝ := fun i j => (cylinderGramDiagonal 0 i)⁻¹ *
      (cylinderGramDiagonal 0 j)⁻¹ *
        (E (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2
    simp only [cylinderTensorWeight, Fin.prod_univ_two] at hsum0
    change (∑ a : Fin 2 → Fin 3, F (a 0) (a 1)) ≤ N.epsilon ^ 2 at hsum0
    rw [sum_two_indices F] at hsum0
    exact hsum0
  have h := weighted_quadratic_le (cylinderGramDiagonal 0)
    (cylinderGramDiagonal_pos (by norm_num))
    (fun i j => E (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j))
    (coordinateComponents v) N.epsilon_pos.le hsum
  rw [← bilinear_quadratic_sum E v, hE v v, modelForm_diagonal z v] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  change (1 - N.epsilon) * RoundCylinderMetric z v v ≤ B z v v ∧
    B z v v ≤ (1 + N.epsilon) * RoundCylinderMetric z v v
  constructor
  · calc
      (1 - N.epsilon) * RoundCylinderMetric z v v =
          RoundCylinderMetric z v v + -(N.epsilon * RoundCylinderMetric z v v) := by ring
      _ ≤ RoundCylinderMetric z v v + (B z v v - RoundCylinderMetric z v v) :=
        add_le_add le_rfl hlo
      _ = B z v v := by ring
  · calc
      B z v v = (B z v v - RoundCylinderMetric z v v) + RoundCylinderMetric z v v := by ring
      _ ≤ N.epsilon * RoundCylinderMetric z v v + RoundCylinderMetric z v v :=
        add_le_add hhi le_rfl
      _ = (1 + N.epsilon) * RoundCylinderMetric z v v := by ring

theorem coordinate_speed_bounds (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderCoordinates) :
    (N.scale / 2) * Real.sqrt (RoundCylinderMetric z v v) ≤
        g.tangentNorm (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) ∧
      g.tangentNorm (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) ≤
        (2 * N.scale) * Real.sqrt (RoundCylinderMetric z v v) := by
  let P := roundCylinderPullback g N.coordinate_map z v v
  let H := RoundCylinderMetric z v v
  have hscale : 0 < N.scale := N.scale_pos
  have hP : 0 ≤ P := by
    dsimp [P, roundCylinderPullback]
    by_cases hv : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v = 0
    · simp [hv]
    · exact (g.pos _ _ hv).le
  have hH : 0 ≤ H := by
    dsimp only [H]
    rw [roundCylinderMetric_self_eq]
    positivity
  have hs : N.scale ^ 2 * (N.scale⁻¹ ^ 2 * P) = P := by
    field_simp [ne_of_gt N.scale_pos]
  obtain ⟨hlo, hhi⟩ := N.normalized_metric_quadratic_bounds z hz v
  change (1 - N.epsilon) * H ≤ N.scale⁻¹ ^ 2 * P at hlo
  change N.scale⁻¹ ^ 2 * P ≤ (1 + N.epsilon) * H at hhi
  have hlow : (1 / 4 : ℝ) * H ≤ N.scale⁻¹ ^ 2 * P :=
    (mul_le_mul_of_nonneg_right (by linarith only [N.epsilon_lt_half]) hH).trans hlo
  have hhigh : N.scale⁻¹ ^ 2 * P ≤ 4 * H :=
    hhi.trans (mul_le_mul_of_nonneg_right (by linarith only [N.epsilon_lt_half]) hH)
  have hlow' := mul_le_mul_of_nonneg_left hlow (sq_nonneg N.scale)
  have hhigh' := mul_le_mul_of_nonneg_left hhigh (sq_nonneg N.scale)
  rw [hs] at hlow' hhigh'
  change (N.scale / 2) * Real.sqrt H ≤ Real.sqrt P ∧
    Real.sqrt P ≤ (2 * N.scale) * Real.sqrt H
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hH, Real.sq_sqrt hP]
    nlinarith only [hlow']
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hH, Real.sq_sqrt hP]
    nlinarith only [hhigh']

theorem coordinate_axial_speed_lower (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderCoordinates) :
    (N.scale / 2) * |v.2| ≤ g.tangentNorm (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) := by
  have hscale : 0 < N.scale := N.scale_pos
  have hmodel : |v.2| ≤ Real.sqrt (RoundCylinderMetric z v v) := by
    rw [roundCylinderMetric_self_eq]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by positivity)]
    nlinarith only [sq_nonneg ‖v.1‖]
  exact (mul_le_mul_of_nonneg_left hmodel (by positivity)).trans
    (N.coordinate_speed_bounds z hz v).1

theorem coordinate_sphere_speed_upper (N : EpsilonNeck g)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (w : EuclideanSpace ℝ (Fin 2)) :
    g.tangentNorm (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (w, 0)) ≤
        4 * N.scale * ‖w‖ := by
  have hscale : 0 < N.scale := N.scale_pos
  have hmodel : Real.sqrt (RoundCylinderMetric z (w, 0) (w, 0)) ≤ 2 * ‖w‖ := by
    rw [roundCylinderMetric_self_eq]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith only [sq_nonneg ‖w‖]
  calc
    _ ≤ (2 * N.scale) * Real.sqrt (RoundCylinderMetric z (w, 0) (w, 0)) :=
      (N.coordinate_speed_bounds z hz (w, 0)).2
    _ ≤ (2 * N.scale) * (2 * ‖w‖) :=
      mul_le_mul_of_nonneg_left hmodel (by positivity)
    _ = 4 * N.scale * ‖w‖ := by ring

end PoincareConjecture.EpsilonNeck
