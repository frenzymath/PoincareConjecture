import PoincareConjecture.Proofs.M30.Thm11_1.TerminalNullPlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

open RicciFlow.Splitting

theorem ricciNullity_eq_one_of_finite_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (hab : a < b) (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection b).curvatureTensorNorm p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric b).inner x v v = 1)
    (hw : (F.metric b).inner x w w = 1)
    (hvw : (F.metric b).inner x v w = 0)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    ∀ y : M, ricciNullity (F.connection b) y = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hvw' : inner ℝ v w = 0 := hvw
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw']
  have hframe : Orthonormal ℝ (({1, 2} : Set (Fin 3)).domRestrict ![0, v, w]) := by
    apply orthonormal_iff_ite.mpr
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 1 ∨ i = 2 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
    have hj' : j = 1 ∨ j = 2 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ v v = 1
      exact hv
    · simpa using hvw'
    · simpa using hwv
    · change inner ℝ w w = 1
      exact hw
  obtain ⟨frame, hframe⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hframe1 : frame 1 = v := by simpa using hframe 1 (by simp)
  have hframe2 : frame 2 = w := by simpa using hframe 2 (by simp)
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature := by
    intro t ht y u z
    exact (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator t ht y) u z
  have hD := hC.tensor_calculus 3 M (F.metric b) (F.connection b)
  have hreaction := curvatureReaction_nonpos_on_finite_terminal_null_plane
    hab hC F hoperator x v w hzero
  obtain ⟨z, hz, hzn⟩ :=
    (F.connection b).exists_ricci_null_vector_of_null_frame_plane hD x (hsec b hb x)
      frame (by simpa only [hframe1, hframe2] using hzero)
      (by simpa only [hframe1, hframe2] using hreaction)
  have hpos : 0 < ricciNullity (F.connection b) x := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨z, (mem_ricciKernel _ _ _).mpr hzn⟩, ?_⟩
    intro heq
    exact hz (congrArg Subtype.val heq)
  obtain ⟨p, hp⟩ := hnonflat
  have hupper := (F.connection b).ricciNullity_le_one_of_nonflat
    hD p (hoperator b hb p) hp
  have hxp := ricciNullity_eq_on_positive_slice hC hab F hsec
    (show b ∈ Ioc a b from ⟨hab, le_rfl⟩) x p
  intro y
  have hxy := ricciNullity_eq_on_positive_slice hC hab F hsec
    (show b ∈ Ioc a b from ⟨hab, le_rfl⟩) x y
  omega

end PoincareConjecture.M30
