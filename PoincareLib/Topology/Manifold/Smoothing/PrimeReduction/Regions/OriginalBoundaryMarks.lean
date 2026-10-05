import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.OriginalStarChartImages

/-!
# Literal marked subsets in the original finite model

The unchanged inverse model identifies every original marked subset.
The geometric singleton intersection law identifies marked vertices.
See PrimeReduction005, section1.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- Literal forward and inverse model formulas retain membership
in every entire original marked subset. See PrimeReduction005. -/
theorem original_model_mem_image_iff
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {R S : Set X} {T : Set E} (H : R ≃ₜ T) (F : X → E) (g : E → R)
    (hHF : ∀ x : R, (H x : E) = F x)
    (hg : ∀ z : T, (g z : X) = (H.symm z : X)) (hSR : S ⊆ R)
    (z : T) : (g z : X) ∈ S ↔ (z : E) ∈ F '' S := by
  have hFg : F (g z) = (z : E) := by
    rw [hg z, ← hHF (H.symm z), H.apply_symm_apply]
  constructor
  · intro hz
    exact ⟨g z, hz, hFg⟩
  · rintro ⟨x, hx, hFx⟩
    have hHx : H ⟨x, hSR hx⟩ = z :=
      Subtype.ext ((hHF ⟨x, hSR hx⟩).trans hFx)
    have hvalue : (g z : X) = x := by
      rw [hg z, ← hHx, H.symm_apply_apply]
    exact hvalue.symm ▸ hx

end PoincareMT.M76

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An original complex vertex in a subcomplex carrier is a vertex
of that subcomplex, by geometric intersection. See PrimeReduction005. -/
theorem vertex_mem_subcomplex_space_iff
    {K A : SimplicialComplex ℝ E} (hAK : A ≤ K) {p : E}
    (hp : p ∈ K.vertices) : p ∈ A.space ↔ p ∈ A.vertices := by
  classical
  constructor
  · intro hpA
    obtain ⟨s, hs, hps⟩ := mem_space_iff.mp hpA
    have hsingleton : p ∈ intrinsicInterior ℝ
        (convexHull ℝ (({p} : Finset E) : Set E)) := by
      simp [intrinsicInterior_singleton]
    have hsub : ({p} : Finset E) ⊆ s :=
      K.subset_of_mem_intrinsicInterior_face hp (hAK hs) hsingleton hps
    exact A.down_closed hs hsub (Finset.singleton_nonempty p)
  · exact fun hpA => A.vertices_subset_space hpA

/-- Fullness supplies a vertex outside the whole marked carrier
for every unmarked face. See PrimeReduction005, section1. -/
theorem exists_vertex_off_full_subcomplex
    {K A : SimplicialComplex ℝ E} (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsA : s ∉ A.faces) :
    ∃ p ∈ s, p ∉ A.space := by
  classical
  by_contra h
  push Not at h
  apply hsA (hfull s hs ?_)
  intro p hp
  have hpK : p ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_nonempty p)
  exact (vertex_mem_subcomplex_space_iff hAK hpK).mp (h p hp)

end Geometry.SimplicialComplex
