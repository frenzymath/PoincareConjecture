import PoincareConjecture.Proofs.M76.Mathlib.ConicalStar
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial

set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_convexJoin_zero_iff (s : Set E) (x : E) :
    x ∈ convexJoin ℝ {0} s ↔ ∃ y ∈ s, ∃ r ∈ Icc (0 : ℝ) 1, x = r • y := by
  rw [mem_convexJoin]
  constructor
  · rintro ⟨z, hz, y, hy, a, b, ha, hb, hab, he⟩
    rw [mem_singleton_iff] at hz
    subst z
    refine ⟨y, hy, b, ⟨hb, by linarith⟩, ?_⟩
    simpa only [smul_zero, zero_add] using he.symm
  · rintro ⟨y, hy, r, hr, rfl⟩
    exact ⟨0, mem_singleton 0, y, hy, 1 - r, r,
      sub_nonneg.mpr hr.2, hr.1, by ring, by simp⟩

theorem LinearMap.injOn_normalize_of_level (L : E →ₗ[ℝ] ℝ) {s : Set E}
    {c : ℝ} (hc : c ≠ 0) (hL : ∀ x ∈ s, L x = c) :
    InjOn (normalize : E → E) s := by
  intro x hx y hy hxy
  have h := congrArg L hxy
  simp only [NormedSpace.normalize, map_smul, hL x hx, hL y hy, smul_eq_mul] at h
  have hnorm : ‖x‖ = ‖y‖ := inv_injective (mul_right_cancel₀ hc h)
  calc
    x = ‖x‖ • normalize x := (norm_smul_normalize x).symm
    _ = ‖y‖ • normalize y := by rw [hnorm, hxy]
    _ = y := norm_smul_normalize y

namespace Geometry.SimplicialComplex

theorem linearIndependent_faces_of_linear_level (K : SimplicialComplex ℝ E)
    (L : E →ₗ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0)
    (hL : ∀ x ∈ K.space, L x = c) :
    ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E) := by
  intro s hs
  exact (K.indep hs).linearIndependent_of_linear_level L hc
    (fun x => hL x (K.subset_space hs x.property))

theorem coneAtZero_space_eq_convexJoin [DecidableEq E] (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hrad : InjOn (normalize : E → E) K.space) (hne : K.space.Nonempty) :
    (K.coneAtZero hlin hrad).space = convexJoin ℝ {0} K.space := by
  ext x
  rw [mem_convexJoin_zero_iff]
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    · obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      have hsub : (s : Set E) ⊆ insert (0 : E) (s.erase 0 : Set E) := by
        intro y hy
        by_cases hy0 : y = 0
        · exact Or.inl hy0
        · exact Or.inr (Finset.mem_erase.mpr ⟨hy0, hy⟩)
      obtain ⟨y, hy, r, hr, hxr⟩ :=
        exists_pos_smul_of_mem_convexHull_insert_zero (convexHull_mono hsub hxs) hx0
      have hsK : s.erase 0 ∈ K.faces := hs.2.resolve_left (fun he => by simp [he] at hy)
      exact ⟨y, K.convexHull_subset_space hsK hy, r, ⟨hr.1.le, hr.2⟩, hxr⟩
  · rintro ⟨y, hy, r, hr, rfl⟩
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
    apply convexHull_subset_space (insert_zero_mem_coneAtZero_faces hlin hrad hs)
    rw [Finset.coe_insert]
    exact smul_mem_convexHull_insert_zero hys hr

theorem exists_finite_cone_of_linear_level (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hne : K.space.Nonempty) (L : E →ₗ[ℝ] ℝ)
    {c : ℝ} (hc : c ≠ 0) (hL : ∀ x ∈ K.space, L x = c) :
    ∃ C : SimplicialComplex ℝ E, C.faces.Finite ∧
      C.space = convexJoin ℝ {0} K.space := by
  classical
  let hlin := K.linearIndependent_faces_of_linear_level L hc hL
  let hrad := L.injOn_normalize_of_level hc hL
  exact ⟨K.coneAtZero hlin hrad, finite_coneAtZero_faces hK hlin hrad,
    K.coneAtZero_space_eq_convexJoin hlin hrad hne⟩

end Geometry.SimplicialComplex
