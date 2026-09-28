import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.DoublePartner
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.InteriorInterval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.BoundaryInterval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.GraphIncidence

set_option autoImplicit false
open Set Geometry Topology Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in
theorem exists_finite_proper_double_graph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (Q : Set E)
    (hf : PolyhedralPLInCharts e f K.space) (hR : MapsTo f K.space R)
    (hclosed : IsClosed (doubleLocusOn f K.space))
    (hproper : ∀ x ∈ K.space, f x ∈ frontier R ↔ x ∈ Q)
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
      (∀ x : G.space, (partner x : E) ∈ Q ↔ (x : E) ∈ Q) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
        if (v : E) ∈ Q then 1 else 2) ∧
      G.space ∩ Q = Subtype.val '' {v : G.vertices |
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  obtain ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate⟩ :=
    exists_finite_source_double_partner he K hK hf hclosed hcross hunique
  have hgerms : ∀ x ∈ G.space, ∃ u v : E, u ≠ x ∧ v ≠ x ∧
      (x ∈ Q → u = v) ∧
      (x ∉ Q → segment ℝ x u ∩ segment ℝ x v ⊆ {x}) ∧
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
    by_cases hxQ : x ∈ Q
    · obtain ⟨u, hu, hnear⟩ := C.exists_boundary_segment_germ hf hR side
        ⟨x, hxK⟩ hside (hGs.subset hx) ((hproper x hxK).mpr hxQ)
      refine ⟨u, u, hu, hu, fun _ => rfl, fun hn => (hn hxQ).elim, ?_⟩
      simpa only [hGs, union_self] using hnear
    · have hint : f x ∈ interior R := by
        by_contra hn
        exact hxQ ((hproper x hxK).mp ⟨subset_closure (hR hxK), hn⟩)
      obtain ⟨u, v, hu, hv, hi, hn⟩ := C.exists_interior_two_segment_germ hf hR side
        ⟨x, hxK⟩ hside (hGs.subset hx) hint
      exact ⟨u, v, hu, hv, fun h => (hxQ h).elim, fun _ => hi, by simpa only [hGs] using hn⟩
  obtain ⟨hcard, hdegree, hrim⟩ :=
    G.face_card_and_degree_of_boundary_segment_germs hG Q hgerms
  refine ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, ?_,
    hcard, hdegree, hrim⟩
  intro x
  rw [← hproper _ (hGs.subset (partner x).property).1,
    ← hproper _ (hGs.subset x.property).1, hvalue]

end PoincareConjecture.M76.Dehn.Annuli
