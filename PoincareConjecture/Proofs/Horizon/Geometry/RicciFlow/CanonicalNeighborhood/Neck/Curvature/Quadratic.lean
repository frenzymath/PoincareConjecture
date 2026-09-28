import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

universe u

namespace PoincareConjecture

open RicciFlow.Splitting Poincare.Geometry.Riemannian.SpaceForm

theorem bilinear_abs_apply_self_le_nine_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    {α : ℝ} (hB : ∀ i j, |B (b i) (b j)| ≤ α) (v : E) :
    |B v v| ≤ 9 * α * ‖v‖ ^ 2 := by
  have hc (i : Fin 3) : |b.repr v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs, b.repr.norm_map] using PiLp.norm_apply_le (b.repr v) i
  have he : B v v = ∑ i : Fin 3, ∑ j : Fin 3,
      b.repr v i * b.repr v j * B (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, b.repr v i * b.repr v j * B (b i) (b j)| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |b.repr v i * b.repr v j * B (b i) (b j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖v‖ * ‖v‖ * α := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hc i) (hc j) (abs_nonneg _) (norm_nonneg _))
        (hB i j) (abs_nonneg _) (mul_self_nonneg _)
    _ = 9 * α * ‖v‖ ^ 2 := by simp; ring

theorem roundCylinderEuclideanMetric_norm_sq_le (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 ≤ roundCylinderEuclideanMetric.inner 0 v v := by
  change ‖v‖ ^ 2 ≤ roundCylinderModelCoefficients
    ((RiemannianMetric.lineModelEquiv 2).symm 0)
    ((RiemannianMetric.lineModelEquiv 2).symm v)
    ((RiemannianMetric.lineModelEquiv 2).symm v)
  simp only [map_zero, roundCylinderModelCoefficients_apply, Prod.fst_zero, norm_zero,
    zero_pow (by norm_num : 2 ≠ 0), zero_add, real_inner_self_eq_norm_sq]
  change ‖v‖ ^ 2 ≤ 2 * (16 / (4 : ℝ) ^ 2) *
    ‖Poincare.EuclideanSpace.euclideanTail v‖ ^ 2 + v 0 * v 0
  norm_num
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp only [Poincare.EuclideanSpace.euclideanTail_apply]
  nlinarith [Finset.sum_nonneg (fun (i : Fin 2) (_ : i ∈ Finset.univ) =>
    sq_nonneg (v i.succ))]

namespace EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem centered_ricci_quadratic_control (N : EpsilonNeck g) (D : LeviCivitaData g)
    (q : UnitTwoSphere) (s : ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hcoeff : ∀ i j : Fin 3,
      |D.ricci (N.centeredEuclideanParametrization q s 0)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis i))
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis j)) -
        (if i = j ∧ i ≠ 2 then 1 else 0)| ≤ α)
    (v : EuclideanSpace ℝ (Fin 3)) :
    |D.ricci (N.centeredEuclideanParametrization q s 0)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v) -
      ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
        ((RiemannianMetric.lineModelEquiv 2).symm v).1⟫_ℝ| ≤
      9 * α * roundCylinderEuclideanMetric.inner 0 v v := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex ((finRotate 3).symm)
  let L := (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0).toLinearMap
  let D₀ := roundCylinderEuclideanMetric.euclideanLeviCivitaData
  let B := (ricciBilinear D (N.centeredEuclideanParametrization q s 0)).compl₁₂ L L -
    ricciBilinear D₀ 0
  have hb (i : Fin 3) : b i = roundCylinderEuclideanBasis i := by
    rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_toBasis]
    rfl
  have hB (i j : Fin 3) : |B (b i) (b j)| ≤ α := by
    simpa only [B, hb, LinearMap.sub_apply, LinearMap.compl₁₂_apply,
      ricciBilinear_apply, roundCylinderEuclideanMetric_ricci_zero_basis, L,
      ContinuousLinearMap.coe_coe] using hcoeff i j
  have h := bilinear_abs_apply_self_le_nine_mul b B hB v
  change |ricciBilinear D (N.centeredEuclideanParametrization q s 0) (L v) (L v) -
    ricciBilinear D₀ 0 v v| ≤ 9 * α * ‖v‖ ^ 2 at h
  rw [ricciBilinear_apply, ricciBilinear_apply, roundCylinderEuclideanMetric_ricci_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (roundCylinderEuclideanMetric_norm_sq_le v)
    (by positivity))

theorem centeredEuclideanParametrization_mfderiv_zero (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0 v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0
          ((RiemannianMetric.lineModelEquiv 2).symm v).1,
          ((RiemannianMetric.lineModelEquiv 2).symm v).2) := by
  rw [N.centeredEuclideanParametrization_mfderiv q s
    (by simpa only [map_zero, add_zero] using hs), map_zero, add_zero]
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm 0 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt
      ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  let L₁ := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  let L₂ := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  have h₁ := hc.comp (0, s) L₁.mdifferentiableAt
  have h₂ := L₂.mdifferentiableAt (x := (0, s))
  have hf := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (c.symm 0, s) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hs⟩))).mdifferentiableAt (by simp)
  have hh := mfderiv_comp (0, s) hf (h₁.prodMk h₂)
  have hL₁ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) L₁ (0, s) = L₁ :=
    L₁.mfderiv_eq
  have hL₂ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) L₂ (0, s) = L₂ :=
    L₂.mfderiv_eq
  rw [mfderiv_prodMk h₁ h₂, mfderiv_comp (0, s) hc L₁.mdifferentiableAt, hL₁, hL₂] at hh
  have hh' := congrArg (fun A => A ((RiemannianMetric.lineModelEquiv 2).symm v)) hh
  change mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (N.centeredParametrization q) (0, s) ((RiemannianMetric.lineModelEquiv 2).symm v) =
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0, s)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0
        ((RiemannianMetric.lineModelEquiv 2).symm v).1,
        ((RiemannianMetric.lineModelEquiv 2).symm v).2) at hh'
  erw [sphere_chart_symm_zero] at hh'
  exact hh'

theorem ricci_product_quadratic_control (N : EpsilonNeck g) (D : LeviCivitaData g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {α : ℝ} (hα : 0 ≤ α)
    (hcoeff : ∀ i j : Fin 3,
      |D.ricci (N.centeredEuclideanParametrization q s 0)
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis i))
        (mfderiv (𝓡 3) (𝓡 3) (N.centeredEuclideanParametrization q s) 0
          (roundCylinderEuclideanBasis j)) -
        (if i = j ∧ i ≠ 2 then 1 else 0)| ≤ α)
    (v : RoundCylinderTangent (q, s)) :
    |D.ricci (N.coordinate_map (q, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) v) -
      (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 (q, s) v v - v.2 ^ 2)| ≤
      9 * α * EvolvingRoundCylinderMetric 0 (q, s) v v := by
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
    rw [N.centeredEuclideanParametrization_mfderiv_zero q hs, hV]
    change (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s))
      (L a, v.2) = _
    rw [ha, Prod.mk.eta]
  have h := N.centered_ricci_quadratic_control D q s hα hcoeff V
  erw [hderiv, hV, hmetric] at h
  rw [centeredEuclideanParametrization_zero] at h
  simpa only [htransverse] using h

theorem exists_ricci_quadratic_control :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
        |D.ricci (N.coordinate_map z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) -
          (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ := exists_ambient_curvature_control.{u}
    (show (0 : ℝ) < 1 / 900 by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε z hz v
  have hc := (hcontrol N D hε z.1 hz.2).2
  have h := N.ricci_product_quadratic_control D z.1 hz.2
    (show (0 : ℝ) ≤ 1 / 900 by norm_num) (fun i j => (hc i j).le) v
  norm_num at h ⊢
  exact h

end EpsilonNeck
end PoincareConjecture
