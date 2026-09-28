import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualBlocks









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_coface_of_mem_dualBlock
    (K : SimplicialComplex ℝ E) [Fintype K.faces] {s : Finset E} {x : E}
    (hx : x ∈ (K.barycentricDualBlock s).space) :
    ∃ t ∈ K.faces, s ⊆ t ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨f, hf, hxf⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha, hchain, hfa⟩ := (K.barycentricSubdivision_faces f).mp hf.1
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  have hcent : m.val.centroid ℝ id ∈ f :=
    hfa.symm ▸ Finset.mem_image.mpr ⟨m, hm, rfl⟩
  obtain ⟨u, hu, hsu, hum⟩ := hf.2 _ hcent
  have humEq : (⟨u, hu⟩ : K.faces) = m := K.faceCentroid_injective hum
  have hum' : u = m.val := congrArg Subtype.val humEq
  refine ⟨m.val, m.property, hum' ▸ hsu, ?_⟩
  apply convexHull_min _ (convex_convexHull ℝ _) hxf
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hfa ▸ hy)
  exact convexHull_mono (him i hi)
    (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))

end Geometry.SimplicialComplex
