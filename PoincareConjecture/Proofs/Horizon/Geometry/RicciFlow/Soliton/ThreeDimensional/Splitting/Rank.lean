import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Curvature.Operator

universe u

namespace PoincareConjecture.LeviCivitaData

open RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem curvatureTensorNorm_eq_zero_of_two_le_ricciNullity
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x)
    (hdim : 2 ≤ ricciNullity D x) : D.curvatureTensorNorm x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  obtain ⟨k, hk⟩ := Poincare.RicciFlow.Splitting.exists_orthonormal_frame hdim
  let e : Fin 2 → TangentSpace (𝓡 3) x := fun i => k i
  have he : Orthonormal ℝ e := (ricciKernel D x).subtypeₗᵢ.orthonormal_comp_iff.mpr hk
  have hframe : Orthonormal ℝ
      (({1, 2} : Set (Fin 3)).domRestrict ![0, e 0, e 1]) := by
    apply orthonormal_iff_ite.mpr
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 1 ∨ i = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
    have hj' : j = 1 ∨ j = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ (e 0) (e 0) = 1
      simpa only [ite_true] using (orthonormal_iff_ite.mp he 0 0)
    · change inner ℝ (e 0) (e 1) = 0
      simpa only [if_neg (by decide : (0 : Fin 2) ≠ 1)] using
        (orthonormal_iff_ite.mp he 0 1)
    · change inner ℝ (e 1) (e 0) = 0
      simpa only [if_neg (by decide : (1 : Fin 2) ≠ 0)] using
        (orthonormal_iff_ite.mp he 1 0)
    · change inner ℝ (e 1) (e 1) = 1
      simpa only [ite_true] using (orthonormal_iff_ite.mp he 1 1)
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb1 : b 1 = e 0 := by simpa using hb 1 (by simp)
  have hb2 : b 2 = e 1 := by simpa using hb 2 (by simp)
  have hsec := D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x hoperator
  have hn1 : D.ricci x (b 1) (b 1) = 0 := by
    rw [hb1]
    exact (mem_ricciKernel D x (e 0)).mp (k 0).property (e 0)
  have hn2 : D.ricci x (b 2) (b 2) = 0 := by
    rw [hb2]
    exact (mem_ricciKernel D x (e 1)).mp (k 1).property (e 1)
  have hflat1 := curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD x hsec hn1
  have hflat2 := curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD x hsec hn2
  have hflat01 : D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) = 0 := by
    rw [D.curvatureTensor_swap_first, hflat1, neg_zero]
  have hscalar : D.scalarCurvature x = 0 := by
    rw [D.scalarCurvature_eq_twice_trace_curvatureOperator hD x b,
      curvatureOperator_trace]
    simp only [Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply,
      curvatureMatrix, pairFirst, pairSecond]
    change 2 * (D.curvatureTensor x (b 1) (b 2) (b 1) (b 2) +
      D.curvatureTensor x (b 2) (b 0) (b 2) (b 0) +
      D.curvatureTensor x (b 0) (b 1) (b 0) (b 1)) = 0
    rw [hflat1, hflat2, hflat01]
    norm_num
  apply le_antisymm _ (Real.sqrt_nonneg _)
  exact (D.curvatureTensorNorm_le_scalarCurvature_sharp hD x hoperator).trans_eq hscalar


theorem ricciNullity_le_one_of_nonflat
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x)
    (hnonflat : D.curvatureTensorNorm x ≠ 0) : ricciNullity D x ≤ 1 := by
  by_contra h
  exact hnonflat (D.curvatureTensorNorm_eq_zero_of_two_le_ricciNullity hD x hoperator
    (by omega))

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow



theorem ricciNullity_eq_one_of_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    ∀ y : M, Splitting.ricciNullity (F.connection 0) y = 1 := by
  obtain ⟨p, hp⟩ := hnonflat
  have hupper := (F.connection 0).ricciNullity_le_one_of_nonflat
    (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)) p (hoperator 0 le_rfl p) hp
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (-1 : ℝ) 0 ⊆ Iic (0 : ℝ) from fun _ hs => hs.2) ordConnected_Icc
    ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hsec : ∀ s ∈ Icc (-1 : ℝ) 0, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a b
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (hoperator s hs.2 q) a b
  intro y
  have hspace := Splitting.ricciNullity_eq_on_positive_slice hC (by norm_num : (-1 : ℝ) < 0)
    G hsec (by norm_num : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0) y p
  change Splitting.ricciNullity (F.connection 0) y =
    Splitting.ricciNullity (F.connection 0) p at hspace
  have hpos : 0 < Splitting.ricciNullity (F.connection 0) y := by
    obtain ⟨z, hz, hzn⟩ := F.exists_ricci_null_vector_on_past_of_terminal_null_plane
      hC hoperator x v w hv hw hvw hzero 0 le_rfl y
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨z, (Splitting.mem_ricciKernel _ _ _).mpr hzn⟩, ?_⟩
    intro heq
    exact hz (congrArg Subtype.val heq)
  omega

end PoincareConjecture.RicciFlow
