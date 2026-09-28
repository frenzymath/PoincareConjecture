import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem FinitePiecewiseAffineOn.exists_interval_breakpoints {f : ℝ → F} {l u : ℝ}
    (hf : FinitePiecewiseAffineOn f (Icc l u)) (hlu : l ≤ u) :
    ∃ T : Finset ℝ, (T : Set ℝ) ⊆ Icc l u ∧ l ∈ T ∧ u ∈ T ∧
      ∀ x y : ℝ, l ≤ x → y ≤ u → x < y → Disjoint (Ioo x y) (T : Set ℝ) →
        ∃ A : ℝ →ᴬ[ℝ] F, EqOn f A (Icc x y) := by
  classical
  obtain ⟨K, hK, hspace, hfaces⟩ := hf
  let T := hK.toFinset.biUnion id ∪ {l, u}
  have hverts {t : Finset ℝ} (ht : t ∈ K.faces) {v : ℝ} (hv : v ∈ t) : v ∈ T :=
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨t, hK.mem_toFinset.mpr ht, hv⟩)
  refine ⟨T, ?_, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
    Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨t, ht, hv⟩ := Finset.mem_biUnion.mp hv
      exact hspace ▸ K.subset_space (hK.mem_toFinset.mp ht) hv
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨le_rfl, hlu⟩
      · rw [Finset.mem_singleton.mp hv]
        exact ⟨hlu, le_rfl⟩
  · intro x y hlx hyu hxy hdisj
    have hm : (x + y) / 2 ∈ K.space := by
      rw [hspace]
      constructor <;> linarith
    obtain ⟨t, ht, hmt⟩ := SimplicialComplex.mem_space_iff.mp hm
    have htne := K.nonempty_of_mem_faces ht
    have hmin := Finset.min'_mem t htne
    have hmax := Finset.max'_mem t htne
    have hbounds : convexHull ℝ (t : Set ℝ) ⊆ Icc (t.min' htne) (t.max' htne) :=
      convexHull_min (fun z hz => ⟨Finset.min'_le t z hz, Finset.le_max' t z hz⟩)
        (convex_Icc _ _)
    have hmb := hbounds hmt
    have hleft : t.min' htne ≤ x := by
      by_contra h
      exact Set.disjoint_left.mp hdisj ⟨lt_of_not_ge h, by linarith [hmb.1]⟩ (hverts ht hmin)
    have hright : y ≤ t.max' htne := by
      by_contra h
      exact Set.disjoint_left.mp hdisj ⟨by linarith [hmb.2], lt_of_not_ge h⟩ (hverts ht hmax)
    have hsegment := (convex_convexHull ℝ (t : Set ℝ)).segment_subset
      (subset_convexHull ℝ _ hmin) (subset_convexHull ℝ _ hmax)
    rw [segment_eq_Icc (Finset.min'_le t _ hmax)] at hsegment
    obtain ⟨A, hA⟩ := hfaces t ht
    exact ⟨A, hA.mono (fun z hz => hsegment ⟨hleft.trans hz.1, hz.2.trans hright⟩)⟩





theorem FinitePiecewiseAffineOn.exists_affine_segment_breakpoints [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    (a : ℝ →ᴬ[ℝ] E) (ha : MapsTo a (Icc (0 : ℝ) 1) s) :
    ∃ T : Finset ℝ, (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 ∧ 0 ∈ T ∧ 1 ∈ T ∧
      ∀ x y : ℝ, 0 ≤ x → y ≤ 1 → x < y → Disjoint (Ioo x y) (T : Set ℝ) →
        ∃ A : ℝ →ᴬ[ℝ] F, EqOn (f ∘ a) A (Icc x y) := by
  classical
  let H : Finset (ℝ →ᵃ[ℝ] ℝ) :=
    {-(AffineMap.id ℝ ℝ), AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 1}
  have hrep : Icc (0 : ℝ) 1 = {t | ∀ B ∈ H, B t ≤ 0} := by
    ext t
    simp [H]
  obtain ⟨K, hK, hspace⟩ := isCompact_Icc.exists_finite_triangulation_of_halfspaces H hrep
  have haf : FinitePiecewiseAffineOn a (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hspace, K.affineOnFaces_affine a⟩
  exact (hf.comp haf ha).exists_interval_breakpoints zero_le_one

end Geometry
