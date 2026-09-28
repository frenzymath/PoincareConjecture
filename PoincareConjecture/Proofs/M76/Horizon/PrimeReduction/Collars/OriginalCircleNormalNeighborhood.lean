import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleNormalSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.PlaneHeight
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTriangleMixedSigns

set_option autoImplicit false
open Set Geometry Module
open scoped Topology

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_triangle_normal_neighborhood
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (H : V3 →ᴬ[ℝ] ℝ) (U : Set V3),
      H.linear ≠ 0 ∧
      (∀ x, H x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E))) ∧
      IsOpen U ∧ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ⊆ U ∧
      ∀ x ∈ U, H x = 0 ↔ x ∈ convexHull ℝ (A '' (s : Set E)) := by
  classical
  let T := convexHull ℝ (A '' (s : Set E))
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hdim : finrank ℝ (affineSpan ℝ (A '' (s : Set E))).direction = 2 := by
    have hi := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull
      (p := ((↑) : s → E)) (K.indep hs) (by rw [Subtype.range_coe]; exact hAi)
    have hrange : range (A.toAffineMap ∘ ((↑) : s → E)) = A '' (s : Set E) := by
      rw [range_comp, Subtype.range_coe]
      rfl
    have hh := hi.finrank_vectorSpan (n := 2) (by simpa using hs3)
    rw [hrange] at hh
    rw [direction_affineSpan]
    exact hh
  have hne : (A '' (s : Set E)).Nonempty :=
    (K.nonempty_of_mem_faces hs).to_set.image A
  obtain ⟨H₀, hH₀, hplane⟩ :=
    (affineSpan ℝ (A '' (s : Set E))).exists_defining_height_of_finrank_two
      (by simp) hdim (hne.mono (subset_affineSpan ℝ _))
  let H : V3 →ᴬ[ℝ] ℝ := ⟨H₀, H₀.continuous_of_finiteDimensional⟩
  let U := interior {x | x ∈ T ↔ x ∈ affineSpan ℝ T}
  refine ⟨H, U, hH₀, hplane, isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr
      (eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hx)
  · intro x hx
    have hxt := interior_subset hx
    change x ∈ T ↔ x ∈ affineSpan ℝ T at hxt
    rw [affineSpan_convexHull] at hxt
    exact (hplane x).trans hxt.symm

end PoincareConjecture.M76
