import PoincareConjecture.Proofs.M76.Mathlib.BasisSecantCones
import PoincareConjecture.Proofs.M76.Mathlib.ClosedConeProjectionBound
import PoincareConjecture.Proofs.M76.Mathlib.RadialConeCarriers










set_option autoImplicit false

open Set

namespace Module.Basis

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem exists_pos_secant_bound_of_injOn (b : Basis ι ℝ E)
    (faces : Set (Finset ι)) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))),
      ∀ y ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))),
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  classical
  let := Fintype.ofFinite ι
  let := b.finiteDimensional_of_finite
  let C : Set E := ⋃ s ∈ faces, ⋃ t ∈ faces, b.secantCone (s : Set ι) (t : Set ι)
  have hclosed : IsClosed C :=
    (Set.toFinite faces).isClosed_biUnion (fun s _ =>
      (Set.toFinite faces).isClosed_biUnion (fun t _ => b.isClosed_secantCone s t))
  have hsmul : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r • x ∈ C := by
    intro x hx r hr
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr
      ⟨t, ht, b.smul_mem_secantCone hxt hr.le⟩⟩
  have hker : ∀ x ∈ C, Q x = 0 → x = 0 := by
    intro x hx he
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    apply b.eq_zero_of_mem_secantCone_of_injOn Q (hQ.mono ?_) hxt he
    exact union_subset (subset_iUnion₂_of_subset s hs Subset.rfl)
      (subset_iUnion₂_of_subset t ht Subset.rfl)
  obtain ⟨c, hc, hb⟩ := Q.exists_pos_norm_lower_bound_on_cone hclosed hsmul hker
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
  have hxc : x ∈ b.nonnegativeCone (s : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    exact ConvexCone.subset_hull hxs
  have hyc : y ∈ b.nonnegativeCone (t : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    exact ConvexCone.subset_hull hyt
  have hxy : x - y ∈ C := mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr ⟨t, ht,
    (b.mem_secantCone_iff s t (x - y)).mpr ⟨x, hxc, y, hyc, rfl⟩⟩⟩
  simpa only [map_sub] using hb (x - y) hxy

end Module.Basis

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {A : AbstractSimplicialComplex ι} {b : Module.Basis ι ℝ E}





theorem BasisRadialProjection.exists_pos_secant_bound (Q : A.BasisRadialProjection b F) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (A.basisRadialEmbedding b).cone.space,
      ∀ y ∈ (A.basisRadialEmbedding b).cone.space,
      c * ‖x - y‖ ≤ ‖Q.val x - Q.val y‖ := by
  have hQ := Q.injOn_basisCone
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact b.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q.val hQ

end AbstractSimplicialComplex
