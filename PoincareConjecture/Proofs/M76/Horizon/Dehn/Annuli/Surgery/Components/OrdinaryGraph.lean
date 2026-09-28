import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.DoublePartner
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.InteriorInterval
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.GraphIncidence








set_option autoImplicit false
open Set Geometry Topology Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in
theorem exists_finite_interior_double_graph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) (hR : MapsTo f K.space R)
    (hclosed : IsClosed (doubleLocusOn f K.space))
    (hinterior : MapsTo f (doubleLocusOn f K.space) (interior R))
    (hcross : ∀ x ∈ K.space, ∀ y ∈ K.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f K.space R x y))
    (hunique : ∀ x ∈ K.space, ∀ y ∈ K.space, ∀ z ∈ K.space,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z) :
    ∃ (G : SimplicialComplex ℝ E) (partner : G.space ≃ₜ G.space),
      G.faces.Finite ∧ G.space = doubleLocusOn f K.space ∧
      partner.IsFinitePL ∧ partner.symm.IsFinitePL ∧ Function.Involutive partner ∧
      (∀ x : G.space, (partner x : E) ≠ x) ∧
      (∀ x : G.space, f (partner x) = f x) ∧
      (∀ (x : G.space) (y : E), y ∈ K.space → (x : E) ≠ y →
        f x = f y → y = (partner x : E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
  obtain ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate⟩ :=
    exists_finite_source_double_partner he K hK hf hclosed hcross hunique
  have hgerms : ∀ x ∈ G.space, ∃ u v : E, u ≠ x ∧ v ≠ x ∧
      segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
      ∀ᶠ z in 𝓝 x, z ∈ G.space ↔ z ∈ segment ℝ x u ∪ segment ℝ x v := by
    intro x hx
    have hxG := hGs.subset hx
    obtain ⟨hxK, y, hyK, hxy, hne⟩ := hxG
    obtain ⟨C⟩ := hcross x hxK y hyK hne hxy
    have hlabel : ∃ side : Bool, x ∈ if side then C.right else C.left := by
      rcases C.labels with h | h
      · exact ⟨false, h.1⟩
      · exact ⟨true, h.1⟩
    obtain ⟨side, hside⟩ := hlabel
    simpa only [hGs] using
      C.exists_interior_two_segment_germ hf hR side ⟨x, hxK⟩ hside
        (hGs.subset hx) (hinterior (hGs.subset hx))
  obtain ⟨hcard, hdegree⟩ := G.face_card_and_degree_of_two_segment_germs hG hgerms
  exact ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hcard, hdegree⟩

end PoincareConjecture.M76.Dehn.Annuli

