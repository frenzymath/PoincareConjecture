import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Reaction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

theorem terminalCurvature_null_evolution_nonpos
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).tensorLaplacian (F.connection b).riemannEvaluation x ![v, w, v, w] +
      (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hmin : IsMinOn (fun t => (F.connection t).curvatureTensor x v w v w)
      (Icc a b) b := by
    intro t ht
    change (F.connection b).curvatureTensor x v w v w ≤ _
    rw [hzero]
    exact hsec t ht x v w
  have hcone : a - b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc a b).segment_subset hb ha)
  have h := hmin.localize.hasFDerivWithinAt_nonneg
    (hC.curvature_evolution n M (Icc a b) F b hb x v w v w).hasFDerivWithinAt hcone
  change 0 ≤ (a - b) * (_ + _) at h
  nlinarith

theorem terminalCurvature_null_reaction_nonpos
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    (F.connection b).curvatureReaction x v w v w ≤ 0 := by
  have he := terminalCurvature_null_evolution_nonpos hC hab F hsec x v w hzero
  have hl := (F.connection b).tensorLaplacian_nonneg_on_null_plane
    (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (hsec b (right_mem_Icc.mpr hab.le)) x v w hzero
  linarith

theorem terminalCurvature_exists_ricci_null_vector
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric b).inner x v v = 1)
    (hw : (F.metric b).inner x w w = 1)
    (hvw : (F.metric b).inner x v w = 0)
    (hzero : (F.connection b).curvatureTensor x v w v w = 0) :
    ∃ z : TangentSpace (𝓡 3) x, z ≠ 0 ∧ ∀ u, (F.connection b).ricci x z u = 0 := by
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
  obtain ⟨e, he⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have he1 : e 1 = v := by simpa using he 1 (by simp)
  have he2 : e 2 = w := by simpa using he 2 (by simp)
  apply (F.connection b).exists_ricci_null_vector_of_null_frame_plane
    (hC.tensor_calculus 3 M (F.metric b) (F.connection b)) x
    (hsec b (right_mem_Icc.mpr hab.le) x) e
  · simpa only [he1, he2] using hzero
  · simpa only [he1, he2] using
      terminalCurvature_null_reaction_nonpos hC hab F hsec x v w hzero

end PoincareConjecture.M47
