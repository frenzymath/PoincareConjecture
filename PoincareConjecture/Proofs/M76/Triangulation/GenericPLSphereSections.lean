import PoincareConjecture.Proofs.M76.Triangulation.PLSphereConnectedHeightSection
import PoincareConjecture.Proofs.M76.Triangulation.IntrinsicRegularSlices
import PoincareConjecture.Proofs.M76.Triangulation.ExceptionalSlicePolygons
import PoincareConjecture.Proofs.M76.Mathlib.GenericSurfaceHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.HalfspaceGraphConnectivity
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedLinkSectionNonisolation

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_intermediate_level_polygon_of_preconnected_signed_links
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hconn : IsPreconnected K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {C : Set F} {e : K.space ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    (hlinkgraphs : ∀ p ∈ K.vertices,
      ((K.link p).vertexAbstractComplex.edgeGraph.induce
        {v : (K.link p).vertices | A (v : E) < A p}).Preconnected ∧
        ((K.link p).vertexAbstractComplex.edgeGraph.induce
          {v : (K.link p).vertices | A p < A (v : E)}).Preconnected)
    {p q : E} (hp : p ∈ K.vertices) (hq : q ∈ K.vertices)
    {c : ℝ} (hpc : A p < c) (hcq : c < A q) :
    ∃ n : ℕ, ∃ P : Polygon E (n + 3),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = K.space ∩ {x | A x = c} := by
  have hgraphs := K.preconnected_signed_sublevel_graphs_of_preconnected_links hK
    (K.preconnected_edgeGraph_of_isPreconnected hK hconn) A hA hlinkgraphs
  have hsides := K.isPreconnected_strict_sides_of_vertex_graphs A c
    (hgraphs c).1 (hgraphs c).2
  have hsigns : ∀ x ∈ K.space, A x = c →
      x ∈ closure (K.space ∩ {y | A y < c}) ∧
        x ∈ closure (K.space ∩ {y | c < A y}) := by
    intro x hx hxc
    have h := K.mem_both_height_closures_of_preconnected_sublevels hK A hA hgraphs
      hx hp hq (hpc.trans_eq hxc.symm) (hxc.trans_lt hcq)
    simpa only [hxc] using h
  by_cases hvertex : ∃ v ∈ K.vertices, A v = c
  · obtain ⟨v, hv, hvc⟩ := hvertex
    let B := A - AffineMap.const ℝ E c
    have hBv : B v = 0 := sub_eq_zero.mpr hvc
    have hzero : ∀ w ∈ K.vertices, B w = 0 → w = v := by
      intro w hw hwB
      exact hA hw hv ((sub_eq_zero.mp hwB).trans hvc.symm)
    obtain ⟨m, n, P, hP, hcover, _⟩ :=
      K.exists_exceptionalSlice_polygons B hK hv hBv hzero hpure hcofaces
    have hcover' : K.space ∩ {x | A x = c} = {v} ∪ ⋃ i, (P i).boundary ℝ := by
      simpa only [B, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply, sub_eq_zero]
        using hcover
    obtain ⟨hn, hpos⟩ := hsigns v (K.vertices_subset_space hv) hvc
    have hvacc := K.mem_closure_punctured_level_of_both_signs hK hv A (hlinks v hv)
      (by simpa only [hvc] using hpos) (by simpa only [hvc] using hn)
    have hvacc' : v ∈ closure ((K.space ∩ {x | A x = c}) \ {v}) := by
      simpa only [hvc] using hvacc
    obtain ⟨z, hz, hzv⟩ := closure_nonempty_iff.mp (nonempty_of_mem hvacc')
    have hzP := (hcover'.subset hz).resolve_left hzv
    obtain ⟨i, _⟩ := mem_iUnion.mp hzP
    have hPs : (P i).boundary ℝ ⊆ K.space ∩ {x | A x = c} :=
      (subset_iUnion (fun j => (P j).boundary ℝ) i).trans
        (subset_union_right.trans hcover'.symm.subset)
    exact ⟨n i, P i, (hP i).1, (hP i).2,
      (he.section_eq_polygon_of_preconnected_signs hC hcv hne hdim A c
        hsides.1 hsides.2 hsigns (P i) (hP i).2 (hP i).1 hPs).symm⟩
  · have hreg : ∀ v ∈ K.vertices, A v ≠ c := fun v hv h => hvertex ⟨v, hv, h⟩
    have hpres := K.hasDisjointPolygonPresentation_regular_level hK hpure hcofaces A hreg
    obtain ⟨x, hx, hxc⟩ := hconn.intermediate_value
      (K.vertices_subset_space hp) (K.vertices_subset_space hq)
      A.continuous_of_finiteDimensional.continuousOn ⟨hpc.le, hcq.le⟩
    exact he.exists_section_polygon_of_preconnected_signs hC hcv hne hdim A c
      hsides.1 hsides.2 hsigns hpres ⟨x, hx, hxc⟩

end Geometry.SimplicialComplex
