import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Germs.Boundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart








set_option autoImplicit false
open Set Geometry Filter Topology
open scoped Topology

namespace PoincareConjecture.M76

theorem exists_boundary_intersection_line_neighborhood
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : Set X) (rim : Set E) (hrim : IsCompact rim)
    (hGs : G.space = {z | z ∈ K.space ∧ g z ∈ S})
    (hboundary : ∀ x ∈ G.space ∩ rim,
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) true)) :
    ∃ (U : Set E) (lines : Finset (AffineSubspace ℝ E)),
      IsOpen U ∧ rim ⊆ U ∧
      (∀ A ∈ lines, Module.finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ G.space ∩ U, ∃ A ∈ lines, x ∈ A := by
  classical
  have hlocal (x : ↑(G.space ∩ rim)) : ∃ (U : Set E) (A : AffineSubspace ℝ E),
      IsOpen U ∧ (x : E) ∈ U ∧ Module.finrank ℝ A.direction ≤ 1 ∧ G.space ∩ U ⊆ A := by
    obtain ⟨C⟩ := hboundary x x.property
    obtain ⟨d, q, hd, hxq, _, hnear⟩ := exists_source_intersection_boundary_germ
      K hK hg hgi C.chart C.compatible C.coordinates C.forwardPL
      (by simpa using C.first_surface) (by simpa using C.second_surface)
      ⟨x, (hGs.subset x.property.1).1⟩ C.center_source C.center_coordinates C.center_zero
    obtain ⟨u, _, hgerm⟩ := hd.exists_segment_germ_of_mem_boundary hxq
    have hline : ∀ᶠ z in 𝓝 (x : E), z ∈ G.space → z ∈ affineSpan ℝ ({(x : E), u} : Set E) := by
      filter_upwards [hnear, hgerm] with z hz hz' hzG
      apply convexHull_subset_affineSpan _
      simpa only [convexHull_pair] using hz'.mp (hz.mp (by simpa only [hGs, mem_ofPred_eq] using hzG))
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hline
    refine ⟨U, affineSpan ℝ ({(x : E), u} : Set E), hU, hxU, ?_, ?_⟩
    · rw [direction_affineSpan]
      exact (collinear_pair ℝ (x : E) u).finrank_le_one
    · exact fun z hz => hUsub hz.2 hz.1
  choose U A hU hxU hAdim hcover using hlocal
  have hGclosed := (G.isCompact_space_of_finite hG).isClosed
  have hcompact : IsCompact (G.space ∩ rim) := hrim.inter_left hGclosed
  obtain ⟨I, hI⟩ := hcompact.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let W : Set E := (⋃ x ∈ I, U x) ∪ G.spaceᶜ
  refine ⟨W, I.image A, (isOpen_iUnion fun x => isOpen_iUnion fun _ => hU x).union
    hGclosed.isOpen_compl, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxG : x ∈ G.space
    · exact Or.inl (hI ⟨hxG, hx⟩)
    · exact Or.inr hxG
  · intro L hL
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hL
    exact hAdim x
  · intro x hx
    rcases hx.2 with hxU | hxG
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hxU
      exact ⟨A y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, hcover y ⟨hx.1, hxy⟩⟩
    · exact (hxG hx.1).elim

end PoincareConjecture.M76
