import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.Realization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.EpsilonNeck

open RicciFlow.Splitting Poincare.Geometry.Riemannian.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

private theorem bilinear_eq_coordinate_sum
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : Module.Basis (Fin 3) ℝ E) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (v : E) :
    B v v = ∑ i, ∑ j, b.repr v i * b.repr v j * B (b i) (b j) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem centered_ricci_quadratic_control_of_epsilon_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    |D.ricci (N.centeredEuclideanParametrization q s 0)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v) -
      ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
        ((RiemannianMetric.lineModelEquiv 2).symm v).1⟫_ℝ| ≤
      (7 / 50 : ℝ) * roundCylinderEuclideanMetric.inner 0 v v := by
  let L := (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0).toLinearMap
  let B := (ricciBilinear D (N.centeredEuclideanParametrization q s 0)).compl₁₂ L L
  let b : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3)
      (0 : EuclideanSpace ℝ (Fin 3))) := roundCylinderEuclideanBasis
  let c := roundCylinderEuclideanBasis.repr v
  have hcoeff (i j : Fin 3) :
      |B (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        NeckCurvature.cylinderRicciDiagonal i j| ≤ NeckCurvature.cylinderRicciError i j := by
    simpa only [B, LinearMap.compl₁₂_apply, ricciBilinear_apply, L,
      ContinuousLinearMap.coe_coe] using N.abs_ambient_ricci_coefficient_sub_le D hε q hs i j
  have hmodel : ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
      ((RiemannianMetric.lineModelEquiv 2).symm v).1⟫_ℝ = c 0 ^ 2 + c 1 ^ 2 := by
    let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
    have hb₀ (i j : Fin 3) : ricciBilinear D₀ 0 (b i) (b j) =
        (if i = j ∧ i ≠ 2 then 1 else 0) := by
      rw [ricciBilinear_apply]
      exact roundCylinderEuclideanMetric_ricci_zero_basis D₀ i j
    rw [← roundCylinderEuclideanMetric_ricci_zero D₀]
    rw [← ricciBilinear_apply]
    rw [bilinear_eq_coordinate_sum b]
    simp only [hb₀, b]
    norm_num [Fin.sum_univ_three, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]
    dsimp [c]
    ring_nf
    rfl
  have hmetric : roundCylinderEuclideanMetric.inner 0 v v =
      2 * c 0 ^ 2 + 2 * c 1 ^ 2 + c 2 ^ 2 := by
    change (roundCylinderEuclideanMetric.euclideanCoefficients 0).toBilinForm v v = _
    rw [bilinear_eq_coordinate_sum roundCylinderEuclideanBasis]
    change (∑ i, ∑ j, c i * c j * roundCylinderEuclideanMetric.inner 0
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) = _
    have hg (i j : Fin 3) : roundCylinderEuclideanMetric.inner 0
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) =
        NeckCurvature.cylinderGramDiagonal i j :=
      congrFun (congrFun roundCylinderEuclideanMetric_gram_zero i) j
    simp_rw [hg]
    norm_num [Fin.sum_univ_three, NeckCurvature.cylinderGramDiagonal,
      Matrix.diagonal_apply, Matrix.cons_val_two, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 2 by decide]
    ring
  have h := NeckCurvature.abs_ricci_quadratic_error_le
    (fun i j => B (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) hcoeff c
  dsimp only [c] at h hmodel hmetric
  erw [← bilinear_eq_coordinate_sum b B v,
    ← hmodel, ← hmetric] at h
  change |ricciBilinear D (N.centeredEuclideanParametrization q s 0) (L v) (L v) -
    ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
      ((RiemannianMetric.lineModelEquiv 2).symm v).1⟫_ℝ| ≤
      (7 / 50 : ℝ) * roundCylinderEuclideanMetric.inner 0 v v at h
  rw [ricciBilinear_apply] at h
  exact h

theorem ricci_quadratic_control_of_epsilon_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    (z : RoundCylinderSpace) (hz : z ∈ N.cylinderDomain) (v : RoundCylinderTangent z) :
    |D.ricci (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) -
      (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
      (7 / 50 : ℝ) * EvolvingRoundCylinderMetric 0 z v v := by
  rcases z with ⟨q, s⟩
  let L := mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0
  have hL : Function.Surjective L := by
    apply LinearMap.surjective_of_injective (f := L.toLinearMap)
    apply (injective_iff_map_eq_zero L).mpr
    intro a ha
    have h := roundSphereMetric_chart_symm_inner q 0 a a
    rw [sphere_chart_symm_zero] at h
    change (roundSphereMetric 2).inner q (L a) (L a) = _ at h
    rw [ha] at h
    norm_num [real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)
  obtain ⟨a, ha⟩ := hL v.1
  let V := RiemannianMetric.lineModelEquiv 2 (a, v.2)
  have hV : (RiemannianMetric.lineModelEquiv 2).symm V = (a, v.2) :=
    (RiemannianMetric.lineModelEquiv 2).symm_apply_apply _
  have hsphere : (roundSphereMetric 2).inner q v.1 v.1 = ⟪a, a⟫_ℝ := by
    have h := roundSphereMetric_chart_symm_inner q 0 a a
    rw [sphere_chart_symm_zero] at h
    change (roundSphereMetric 2).inner q (L a) (L a) = _ at h
    rw [ha] at h
    norm_num only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, one_mul] at h
    exact h
  have hmetric : roundCylinderEuclideanMetric.inner 0 V V =
      EvolvingRoundCylinderMetric 0 (q, s) v v := by
    change roundCylinderModelCoefficients ((RiemannianMetric.lineModelEquiv 2).symm 0)
      ((RiemannianMetric.lineModelEquiv 2).symm V)
      ((RiemannianMetric.lineModelEquiv 2).symm V) = _
    rw [map_zero, hV, roundCylinderModelCoefficients_apply]
    change _ = 2 * (1 - 0) * (roundSphereMetric 2).inner q v.1 v.1 + v.2 * v.2
    rw [hsphere]
    norm_num only [Prod.fst_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add,
      sub_zero, mul_one]
  have htransverse : ⟪a, a⟫_ℝ =
      (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 (q, s) v v - v.2 ^ 2) := by
    change _ = (1 / 2 : ℝ) *
      (2 * (1 - 0) * (roundSphereMetric 2).inner q v.1 v.1 + v.2 * v.2 - v.2 ^ 2)
    rw [hsphere]
    ring
  have hderiv : mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 V =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) v := by
    rw [N.centeredEuclideanParametrization_mfderiv_zero q hz.2, hV]
    change (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s))
      (L a, v.2) = _
    rw [ha, Prod.mk.eta]
  have h := N.centered_ricci_quadratic_control_of_epsilon_le D hε q hz.2 V
  erw [hderiv, hV, hmetric] at h
  rw [centeredEuclideanParametrization_zero] at h
  simpa only [htransverse] using h

end PoincareConjecture.EpsilonNeck
