import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.NullPlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.CurvatureNullity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciPropagation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Curvature.Operator

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_ricci_null_vector_of_null_frame_plane
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hsec : ∀ u z : TangentSpace (𝓡 3) x,
      0 ≤ D.curvatureTensor x u z u z) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)),
      D.curvatureTensor x (b 1) (b 2) (b 1) (b 2) = 0 →
      D.curvatureReaction x (b 1) (b 2) (b 1) (b 2) ≤ 0 →
      ∃ v : TangentSpace (𝓡 3) x, v ≠ 0 ∧ ∀ w, D.ricci x v w = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b hzero hreaction
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  let A := curvatureMatrix R
  have hA (i j) : A i j = R (pairFirst i) (pairSecond i)
      (pairFirst j) (pairSecond j) := rfl
  have hsym (i j) : A i j = A j i := (hD.2.2.2.1 x _ _ _ _).2.1
  have h00 : A 0 0 = 0 := hzero
  have h01 : A 0 1 = 0 := by
    change D.curvatureTensor x (b 1) (b 2) (b 2) (b 0) = 0
    rw [D.curvatureTensor_swap_last, (hD.2.2.2.1 x (b 1) (b 2) (b 0) (b 2)).2.1]
    rw [D.curvatureTensor_radial_eq_zero_of_null_plane hD x hsec hzero, neg_zero]
  have h02 : A 0 2 = 0 := by
    have hz : D.curvatureTensor x (b 2) (b 1) (b 2) (b 1) = 0 := by
      rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg, hzero]
    change D.curvatureTensor x (b 1) (b 2) (b 0) (b 1) = 0
    rw [D.curvatureTensor_swap_first, (hD.2.2.2.1 x (b 2) (b 1) (b 0) (b 1)).2.1]
    rw [D.curvatureTensor_radial_eq_zero_of_null_plane hD x hsec hz, neg_zero]
  have hreact : Poincare.Geometry.Curvature.Operator.curvatureReaction A 0 0 ≤ 0 := by
    rw [← D.curvatureB_cyclic_reaction hD x b 0 0]
    exact (D.curvatureReaction_null_plane_eq_curvatureB hD x hsec hzero) ▸ hreaction
  have hdet : A 1 1 * A 2 2 - A 1 2 ^ 2 ≤ 0 := by
    simp only [Poincare.Geometry.Curvature.Operator.curvatureReaction,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply,
      Fin.sum_univ_three, h00, h01, h02, zero_mul, zero_add,
      Matrix.adjugate_fin_three] at hreact
    change 2 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) ≤ 0 at hreact
    rw [hsym 2 1] at hreact
    nlinarith
  have hRic (v : TangentSpace (𝓡 3) x) : 0 ≤ D.ricci x v v :=
    Finset.sum_nonneg fun i _ => hsec v (g.orthonormalBasis x i)
  have hdiag (i j) : D.ricci x (b i) (b j) =
      (D.scalarCurvature x / 2) * (if i = j then 1 else 0) - A i j := by
    have h := D.ricciComplementTensor_apply_orthonormalBasis hD x b i j
    rw [D.ricciComplementTensor_apply] at h
    change (D.scalarCurvature x / 2) * inner ℝ (b i) (b j) -
      D.ricci x (b i) (b j) = A i j at h
    rw [b.inner_eq_ite] at h
    linarith
  have htrace : D.scalarCurvature x / 2 = A 1 1 + A 2 2 := by
    rw [D.scalarCurvature_eq_twice_trace_curvatureOperator hD x b,
      curvatureOperator_trace]
    change 2 * Matrix.trace A / 2 = _
    simp only [Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply, h00]
    ring
  have h11 : D.ricci x (b 1) (b 1) = A 2 2 := by rw [hdiag, htrace]; norm_num
  have h22 : D.ricci x (b 2) (b 2) = A 1 1 := by rw [hdiag, htrace]; norm_num
  have h12 : D.ricci x (b 1) (b 2) = -A 1 2 := by
    rw [hdiag, if_neg (by decide : (1 : Fin 3) ≠ 2), mul_zero, zero_sub]
  have h21 : D.ricci x (b 2) (b 1) = -A 1 2 := by
    rw [(hD.2.2.2.1 x (b 2) (b 1) (b 2) (b 1)).2.2.2, h12]
  by_cases hA11 : A 1 1 = 0
  · refine ⟨b 2, b.orthonormal.ne_zero 2, ?_⟩
    exact PoincareConjecture.RicciFlow.Splitting.ricci_eq_zero_of_nonneg_of_self_eq_zero
      D hD x hRic (h22.trans hA11)
  · let v := (A 1 1) • b 1 + (A 1 2) • b 2
    have hv : v ≠ 0 := by
      intro hz
      have h := congrArg (fun z => inner ℝ z (b 1)) hz
      simp only [v, inner_add_left, real_inner_smul_left, b.inner_eq_ite] at h
      simp only [ite_true, if_neg (by decide : (2 : Fin 3) ≠ 1),
        mul_one, mul_zero, add_zero, inner_zero_left] at h
      exact hA11 h
    have hvalue : D.ricci x v v = A 1 1 * (A 1 1 * A 2 2 - A 1 2 ^ 2) := by
      let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 3) x) :=
        ∑ i, D.curvatureTensor_bilinear_first_third x
          (g.orthonormalBasis x i) (g.orthonormalBasis x i)
      have hB (u w) : B u w = D.ricci x u w := by
        simp [B, LeviCivitaData.ricci, LinearMap.sum_apply]
      rw [← hB]
      simp only [v, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hB, h11, h22, h12, h21]
      ring
    have hnull : D.ricci x v v = 0 := by
      apply le_antisymm _ (hRic v)
      rw [hvalue]
      exact mul_nonpos_of_nonneg_of_nonpos (h22 ▸ hRic (b 2)) hdet
    exact ⟨v, hv, PoincareConjecture.RicciFlow.Splitting.ricci_eq_zero_of_nonneg_of_self_eq_zero
      D hD x hRic hnull⟩

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

theorem exists_ricci_null_vector_of_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∃ z : TangentSpace (𝓡 3) x, z ≠ 0 ∧ ∀ u, (F.connection 0).ricci x z u = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hvw' : inner ℝ v w = 0 := hvw
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw']
  have hframe : Orthonormal ℝ (({1, 2} : Set (Fin 3)).domRestrict ![0, v, w]) := by
    apply orthonormal_iff_ite.mpr
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 1 ∨ i = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
    have hj' : j = 1 ∨ j = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ v v = 1
      exact hv
    · simpa using hvw'
    · simpa using hwv
    · change inner ℝ w w = 1
      exact hw
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb1 : b 1 = v := by simpa using hb 1 (by simp)
  have hb2 : b 2 = w := by simpa using hb 2 (by simp)
  have hD := hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)
  apply (F.connection 0).exists_ricci_null_vector_of_null_frame_plane hD x
    (fun u z => (F.connection 0).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator 0 le_rfl x) u z) b
  · simpa only [hb1, hb2] using hzero
  · simpa only [hb1, hb2] using
      F.curvatureReaction_nonpos_on_terminal_null_plane hC hoperator x v w hzero

theorem exists_ricci_null_vector_on_past_of_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∀ t ≤ 0, ∀ y : M, ∃ z : TangentSpace (𝓡 3) y,
      z ≠ 0 ∧ ∀ u, (F.connection t).ricci y z u = 0 := by
  obtain ⟨z, hz, hzn⟩ := F.exists_ricci_null_vector_of_terminal_null_plane
    hC hoperator x v w hv hw hvw hzero
  have hpos : 0 < Splitting.ricciNullity (F.connection 0) x := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨z, (Splitting.mem_ricciKernel _ _ _).mpr hzn⟩, ?_⟩
    intro heq
    exact hz (congrArg Subtype.val heq)
  intro t ht y
  have hab : t - 1 < (0 : ℝ) := by linarith
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (t - 1) 0 ⊆ Iic (0 : ℝ) from fun _ hs => hs.2) ordConnected_Icc
    ⟨t - 1, left_mem_Icc.mpr hab.le, 0, right_mem_Icc.mpr hab.le, hab.ne⟩
  have hsec : ∀ s ∈ Icc (t - 1) 0, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs p a b
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      p (hoperator s hs.2 p) a b
  have hpast := Splitting.ricciNullity_antitoneOn hC hab G hsec x
    (show t ∈ Icc (t - 1) 0 from ⟨by linarith, ht⟩)
    (right_mem_Icc.mpr hab.le) ht
  have hspace := Splitting.ricciNullity_eq_on_positive_slice hC hab G hsec
    (show t ∈ Ioc (t - 1) 0 from ⟨by linarith, ht⟩) x y
  have hposy : 0 < Splitting.ricciNullity (F.connection t) y := by
    change 0 < Splitting.ricciNullity (G.connection t) y
    rw [← hspace]
    exact hpos.trans_le hpast
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hposy
  refine ⟨z, ?_, (Splitting.mem_ricciKernel _ _ _).mp z.property⟩
  intro heq
  exact hz (Subtype.ext heq)

end PoincareConjecture.RicciFlow
