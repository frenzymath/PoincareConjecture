import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalSideRefinement
import PoincareConjecture.Proofs.M25.Topology3D.Plane.LocalRegionSides
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.LocalSides
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionNesting











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

private theorem local_sides_eq_inter_regions {X : Type*} {W C I O A B : Set X}
    (hdis : Disjoint I O) (hcover : I ∪ O = Cᶜ) (hlocal : A ∪ B = W \ C)
    (hAI : A ⊆ I) (hBO : B ⊆ O) : A = W ∩ I ∧ B = W ∩ O := by
  constructor
  · ext x
    constructor
    · intro hx
      exact ⟨(show x ∈ W \ C from hlocal ▸ Or.inl hx).1, hAI hx⟩
    · rintro ⟨hxW, hxI⟩
      have hxC : x ∈ Cᶜ := hcover ▸ Or.inl hxI
      have hxAB : x ∈ A ∪ B := hlocal.symm ▸ (show x ∈ W \ C from ⟨hxW, hxC⟩)
      exact hxAB.resolve_right fun hxB => Set.disjoint_left.mp hdis hxI (hBO hxB)
  · ext x
    constructor
    · intro hx
      exact ⟨(show x ∈ W \ C from hlocal ▸ Or.inr hx).1, hBO hx⟩
    · rintro ⟨hxW, hxO⟩
      have hxC : x ∈ Cᶜ := hcover ▸ Or.inr hxO
      have hxAB : x ∈ A ∪ B := hlocal.symm ▸ (show x ∈ W \ C from ⟨hxW, hxC⟩)
      exact hxAB.resolve_left fun hxA => Set.disjoint_left.mp hdis (hAI hxA) hxO

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n m : ℕ} {p : Polygon E n} {q : Polygon E m}



theorem IsSimplePolygon.exists_local_two_sides_within (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (x : E) (hx : x ∈ p.boundary ℝ)
    (V : Set E) (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ W A B : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsConnected A ∧ IsConnected B ∧
      A ∪ B = W \ p.boundary ℝ ∧ p.boundary ℝ ∩ W ⊆ closure A ∧
      p.boundary ℝ ∩ W ⊆ closure B := by
  obtain ⟨a, b, ha, hb, hinter, U, hU, hxU, hUC⟩ := hp.exists_local_two_segments x hx
  obtain ⟨e, g, hg, U', hU', hxU', hgraph⟩ :=
    exists_local_graph_two_segments hdim ha hb hinter
  let e' := e.trans (graphFlatteningHomeomorph g hg)
  have hstraight (z : E) (hz : z ∈ U ∩ U') :
      z ∈ p.boundary ℝ ↔ (e' z).2 = 0 := by
    change z ∈ p.boundary ℝ ↔ (e z).2 - g (e z).1 = 0
    rw [sub_eq_zero]
    exact (hUC z hz.1).trans (hgraph z hz.2)
  obtain ⟨W, A, B, hW, hxW, hWV, hA, hB, hlocal, hCA, hCB⟩ :=
    exists_local_two_sides_within_of_straightening e' (hU.inter hU')
      ⟨hxU, hxU'⟩ hx hstraight hV hxV
  exact ⟨W, A, B, hW, hxW, fun _ hz => (hWV hz).2, hA, hB, hlocal, hCA, hCB⟩



theorem IsSimplePolygon.exists_local_region_sides_within (hp : IsSimplePolygon p)
    (hdim : Module.finrank ℝ E = 2) (x : E) (hx : x ∈ p.boundary ℝ)
    (V : Set E) (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      IsConnected (W ∩ polygonInterior p) ∧ IsConnected (W ∩ polygonExterior p) ∧
      (W ∩ polygonInterior p) ∪ (W ∩ polygonExterior p) = W \ p.boundary ℝ := by
  obtain ⟨W, A, B, hW, hxW, hWV, hA, hB, hlocal, _, _⟩ :=
    hp.exists_local_two_sides_within hdim x hx V hV hxV
  obtain ⟨hI, hO, _, _, hdis, hcover, _, _, hIf, hOf⟩ := hp.polygonRegions_spec hdim
  have hxOf : x ∈ frontier (polygonExterior p) := hOf.symm ▸ hx
  obtain ⟨y, hyW, hyO⟩ := mem_closure_iff.mp (frontier_subset_closure hxOf) W hW hxW
  have hyAB : y ∈ A ∪ B :=
    hlocal.symm ▸ (show y ∈ W \ p.boundary ℝ from ⟨hyW, hyO.1⟩)
  have hfinish (A B : Set E) (hA : IsConnected A) (hB : IsConnected B)
      (hlocal : A ∪ B = W \ p.boundary ℝ) (hyB : y ∈ B) :
      IsConnected (W ∩ polygonInterior p) ∧ IsConnected (W ∩ polygonExterior p) ∧
        (W ∩ polygonInterior p) ∪ (W ∩ polygonExterior p) = W \ p.boundary ℝ := by
    obtain ⟨hAI, hBO⟩ := preconnected_local_sides_subset_regions hI hO hdis hcover
      hW hxW (hIf.symm ▸ hx) hA.isPreconnected hB.isPreconnected hlocal ⟨y, hyB, hyO⟩
    obtain ⟨hAe, hBe⟩ := local_sides_eq_inter_regions hdis hcover hlocal hAI hBO
    exact ⟨hAe ▸ hA, hBe ▸ hB, hAe ▸ hBe ▸ hlocal⟩
  refine ⟨W, hW, hxW, hWV, ?_⟩
  rcases hyAB with hyA | hyB
  · exact hfinish B A hB hA ((union_comm B A).trans hlocal) hyA
  · exact hfinish A B hA hB hlocal hyB



theorem IsSimplePolygon.exists_local_regions_eq_of_boundary_agreement
    (hp : IsSimplePolygon p) (hq : IsSimplePolygon q) (hdim : Module.finrank ℝ E = 2)
    (hboundary : q.boundary ℝ ⊆ closure (polygonInterior p))
    (x : E) (hx : x ∈ p.boundary ℝ) (V : Set E) (hV : IsOpen V) (hxV : x ∈ V)
    (heq : ∀ z ∈ V, z ∈ p.boundary ℝ ↔ z ∈ q.boundary ℝ) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      W ∩ polygonInterior p = W ∩ polygonInterior q ∧
      W ∩ polygonExterior p = W ∩ polygonExterior q := by
  obtain ⟨W, hW, hxW, hWV, hA, hB, hlocal⟩ :=
    hp.exists_local_region_sides_within hdim x hx V hV hxV
  obtain ⟨hIq, hOq, _, _, hdis, hcover, _, _, hIf, _⟩ := hq.polygonRegions_spec hdim
  have hlocalq : (W ∩ polygonInterior p) ∪ (W ∩ polygonExterior p) =
      W \ q.boundary ℝ := by
    rw [hlocal]
    ext z
    constructor
    · rintro ⟨hzW, hzC⟩
      exact ⟨hzW, fun hz => hzC ((heq z (hWV hzW)).mpr hz)⟩
    · rintro ⟨hzW, hzC⟩
      exact ⟨hzW, fun hz => hzC ((heq z (hWV hzW)).mp hz)⟩
  have houtside := hp.polygonExterior_subset_of_boundary_subset_closureInterior
    hq hdim hboundary
  obtain ⟨y, hyW, hyO⟩ := hB.nonempty
  obtain ⟨hAI, hBO⟩ := preconnected_local_sides_subset_regions hIq hOq hdis hcover
    hW hxW (hIf.symm ▸ (heq x hxV).mp hx) hA.isPreconnected hB.isPreconnected
    hlocalq ⟨y, ⟨hyW, hyO⟩, houtside hyO⟩
  exact ⟨W, hW, hxW, hWV, local_sides_eq_inter_regions hdis hcover hlocalq hAI hBO⟩

end PoincareConjecture.M25.Topology3D
