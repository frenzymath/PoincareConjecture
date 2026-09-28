import PoincareConjecture.Proofs.M76.Mathlib.VertexStarChartRestriction










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X] [TopologicalSpace V]




theorem exists_original_open_neighborhood_of_closedStar
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (B : OpenPartialHomeomorph X V)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source) :
    InjOn (fun z => B (g z)) (K.closedStar p).space ∧
      ∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ B.source ∧
        O ∩ R ⊆ (fun z => (g z : X)) '' (K.closedStar p).space := by
  let S := (K.closedStar p).space
  have hSK : S ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact K.convexHull_subset_space hs.1 hxs
  have hpK : p ∈ K.space := K.vertices_subset_space hp
  let pK : K.space := ⟨p, hpK⟩
  have hstar : K.closedFaceStar {p} = K.closedStar p := by
    ext s
    simp only [closedFaceStar, closedStar, Finset.singleton_union]
  have hS : Subtype.val ⁻¹' S ∈ 𝓝 pK := by
    change Subtype.val ⁻¹' (K.closedStar p).space ∈ 𝓝 pK
    rw [← hstar]
    exact K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp pK (by
      simp [pK, intrinsicInterior_singleton])
  have hpS : p ∈ S := (show pK ∈ Subtype.val ⁻¹' S from mem_of_mem_nhds hS)
  have hgp : g p = H.symm pK := Subtype.ext (hg pK)
  have hHgp : H (g p) = pK := by rw [hgp, H.apply_symm_apply]
  have hT : H ⁻¹' (Subtype.val ⁻¹' S) ∈ 𝓝 (g p) := by
    have h := H.continuous.continuousAt.preimage_mem_nhds
      (show Subtype.val ⁻¹' S ∈ 𝓝 (H (g p)) by rw [hHgp]; exact hS)
    exact h
  obtain ⟨U, hU, hUT⟩ := (mem_nhds_subtype R (g p) _).mp hT
  obtain ⟨O, hOU, hO, hpO⟩ := mem_nhds_iff.mp
    (inter_mem hU (B.open_source.mem_nhds (hsource hpS)))
  refine ⟨?_, O, hO, hpO, fun x hx => (hOU hx).2, ?_⟩
  · intro x hx y hy hxy
    have hxy' : (g x : X) = (g y : X) := B.injOn (hsource hx) (hsource hy) hxy
    have hgi : H.symm (⟨x, hSK hx⟩ : K.space) = H.symm ⟨y, hSK hy⟩ :=
      Subtype.ext ((hg ⟨x, hSK hx⟩).symm.trans (hxy'.trans (hg ⟨y, hSK hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hgi)
  · intro x hx
    let xR : R := ⟨x, hx.2⟩
    have hxS : (H xR : E) ∈ S := hUT (show xR ∈ Subtype.val ⁻¹' U from (hOU hx.1).1)
    refine ⟨H xR, hxS, ?_⟩
    exact (hg (H xR)).trans (congrArg Subtype.val (H.symm_apply_apply xR))

end Geometry.SimplicialComplex
