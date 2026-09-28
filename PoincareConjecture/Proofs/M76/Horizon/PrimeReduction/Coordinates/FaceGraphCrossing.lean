import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineVertexCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AmbientSurfaceRefinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.GraphDegreeGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicAffineGerms











set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem exists_face_graph_crossing_chart
    (J M G : SimplicialComplex ℝ V3)
    (hJ : J.faces.Finite) (hM : M.faces.Finite) (hMJ : M.space ⊆ J.space)
    (hbound : ∀ a ∈ M.faces, a.card ≤ 3)
    (hG : G.faces.Finite) (hGbound : ∀ a ∈ G.faces, a.card ≤ 2)
    {t : Finset V3} (hGs : G.space = M.space ∩ convexHull ℝ (t : Set V3))
    (htJ : convexHull ℝ (t : Set V3) ⊆ interior J.space)
    (height : V3 →ᵃ[ℝ] ℝ)
    (hheight : ∀ x, height x = 0 ↔ x ∈ affineSpan ℝ (t : Set V3))
    {p : V3} (hpM : p ∈ M.space)
    (hpt : p ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set V3)))
    (hdegree : ∀ hpG : p ∈ G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpG⟩).ncard = 2)
    {d rim : Set V3} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdM : d ⊆ M.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen ((Subtype.val : M.space → V3) ⁻¹' (d \ rim)))
    (hneg : p ∈ closure (M.space ∩ {x | height x < 0}))
    (hpos : p ∈ closure (M.space ∩ {x | 0 < height x}))
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ B : OpenPartialHomeomorph V3 C3,
      p ∈ B.source ∧ B.source ⊆ O ∧ B p = 0 ∧
      LocallyPiecewiseAffineOn B B.source ∧
      LocallyPiecewiseAffineOn B.symm B.target ∧
      (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
      ∀ x ∈ B.source, x ∈ convexHull ℝ (t : Set V3) ↔ (B x).1.1 = 0 := by
  classical
  have hpG : p ∈ G.space := hGs.symm.subset ⟨hpM, intrinsicInterior_subset hpt⟩
  obtain ⟨u, v, hu, hv, hinter, hgerm⟩ :=
    G.exists_two_segment_germ_of_degree_two hG hGbound hpG hdegree
  obtain ⟨U, hU, hpU, hUeq⟩ := Set.exists_open_affine_germ_of_mem_intrinsicInterior hpt
  have htarget (x : V3) (hx : x ∈ U) :
      x ∈ convexHull ℝ (t : Set V3) ↔ height x = 0 := by
    have h := hUeq x hx
    rw [affineSpan_convexHull] at h
    exact h.trans (hheight x).symm
  have hsection : ∀ᶠ x in 𝓝 p,
      x ∈ M.space ∩ {x | height x = 0} ↔
        x ∈ segment ℝ p u ∪ segment ℝ p v := by
    filter_upwards [hgerm, hU.mem_nhds hpU] with x hx hxU
    rw [hGs, mem_inter_iff, htarget x hxU] at hx
    exact hx
  obtain ⟨K, L, hK, _, _, hLK, _, hLM, _, _, hpL, hpK, hLb, _⟩ :=
    J.exists_marked_full_surface_refinement M hJ hM hMJ hbound hpM
      (htJ (intrinsicInterior_subset hpt))
  have hopenL : IsOpen ((Subtype.val : L.space → V3) ⁻¹' (d \ rim)) := by
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
    apply isOpen_induced_iff.mpr
    refine ⟨V, hV, ?_⟩
    ext x
    exact Set.ext_iff.mp hVeq ⟨x, hLM.subset x.property⟩
  obtain ⟨B, hpB, hBO, hBp, hB, hBinv, hBM, hBt, _⟩ :=
    K.exists_affine_vertex_crossing_chart_of_local_disk L hK hLK hLb hpL hpK hd
      (hdM.trans hLM.symm.subset) hpd hopenL
      height hu hv hinter (by simpa only [hLM] using hsection)
      (by simpa only [hLM] using hneg) (by simpa only [hLM] using hpos)
      (hO.inter hU) ⟨hpO, hpU⟩
  refine ⟨B, hpB, fun _ hx => (hBO hx).1, hBp, hB, hBinv, ?_, ?_⟩
  · simpa only [hLM] using hBM
  · intro x hx
    exact (htarget x (hBO hx).2).trans (hBt x hx)

end Geometry.SimplicialComplex
