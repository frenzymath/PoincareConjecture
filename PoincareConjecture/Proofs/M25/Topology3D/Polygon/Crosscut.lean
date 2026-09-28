import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CrosscutPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.LocalRegionComparison











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n m : ℕ} {p : Polygon E n} {q : Polygon E (m + 2)}



theorem IsSimplePolygon.crosscut_intersects_preconnected
    (hp : IsSimplePolygon p) (hq : IsSimplePolygonalArc q) (hdim : Module.finrank ℝ E = 2)
    (a b : Fin n) (hab : b ≠ a) (hfirst : q 0 = p a)
    (hlast : q (Fin.last (m + 1)) = p b)
    (hinside : polygonArcBoundary q \ {p a, p b} ⊆ polygonInterior p)
    (S : Set E) (hS : IsPreconnected S) (hSI : S ⊆ polygonInterior p) (r s : E)
    (hr : r ∈ polygonCyclicPathBoundary p a b \ {p a, p b})
    (hs : s ∈ polygonCyclicPathBoundary p b a \ {p a, p b})
    (hrS : r ∈ closure S) (hsS : s ∈ closure S) :
    (S ∩ (polygonArcBoundary q \ {p a, p b})).Nonempty := by
  classical
  have havoid : Disjoint (polygonArcBoundary q \ {p a, p b}) (p.boundary ℝ) :=
    Set.disjoint_left.mpr fun _ hx hxB => (hinside hx).1 hxB
  obtain ⟨P, hP, hPB⟩ :=
    hp.exists_polygon_of_boundary_path_and_crosscut hq a b hab hfirst hlast havoid
  have hends : ({p a, p b} : Set E) ⊆ p.boundary ℝ := by
    rintro x (rfl | rfl) <;> exact polygon_vertex_mem_boundary p _
  have hboundary : P.boundary ℝ ⊆ closure (polygonInterior p) := by
    rw [hPB, hp.closure_polygonInterior hdim]
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr (polygonCyclicPathBoundary_subset_boundary p a b hx)
    · by_cases he : x ∈ ({p a, p b} : Set E)
      · exact Or.inr (hends he)
      · exact Or.inl (hinside ⟨hx, he⟩)
  have hPI := (hp.polygonRegions_subset_of_boundary_subset_closureInterior hP hdim hboundary).1
  have hcontact {x : E} (hxB : x ∈ p.boundary ℝ) (hxE : x ∉ ({p a, p b} : Set E)) :
      x ∉ polygonArcBoundary q := fun hxA => (hinside ⟨hxA, hxE⟩).1 hxB
  have hrB := polygonCyclicPathBoundary_subset_boundary p a b hr.1
  have hsB := polygonCyclicPathBoundary_subset_boundary p b a hs.1
  have hrM : r ∉ polygonCyclicPathBoundary p b a := fun hrM =>
    hr.2 ((hp.polygonCyclicPathBoundary_inter a b hab) ▸ ⟨hr.1, hrM⟩)
  have hsL : s ∉ polygonCyclicPathBoundary p a b := fun hsL =>
    hs.2 ((hp.polygonCyclicPathBoundary_inter a b hab) ▸ ⟨hsL, hs.1⟩)
  let V := (polygonArcBoundary q ∪ polygonCyclicPathBoundary p b a)ᶜ
  have hV : IsOpen V := ((polygon_arcBoundary_isCompact q).union
    (polygonCyclicPathBoundary_isCompact p b a)).isClosed.isOpen_compl
  have hrV : r ∈ V := fun hh => hh.elim (hcontact hrB hr.2) hrM
  have heq (z : E) (hz : z ∈ V) : z ∈ p.boundary ℝ ↔ z ∈ P.boundary ℝ := by
    rw [← polygonCyclicPathBoundary_union p a b hab, hPB]
    constructor
    · rintro (hzL | hzM)
      · exact Or.inl hzL
      · exact (hz (Or.inr hzM)).elim
    · rintro (hzL | hzA)
      · exact Or.inl hzL
      · exact (hz (Or.inl hzA)).elim
  obtain ⟨W, hW, hrW, _, hWI, _⟩ :=
    hp.exists_local_regions_eq_of_boundary_agreement hP hdim hboundary r hrB V hV hrV heq
  obtain ⟨x, hxW, hxS⟩ := mem_closure_iff.mp hrS W hW hrW
  have hxP : x ∈ polygonInterior P :=
    (show x ∈ W ∩ polygonInterior P from hWI ▸ ⟨hxW, hSI hxS⟩).2
  obtain ⟨hIP, hOP, _, _, hdis, hcover, _⟩ := hP.polygonRegions_spec hdim
  have hsPB : s ∉ P.boundary ℝ := by
    rw [hPB]
    exact fun hh => hh.elim hsL (hcontact hsB hs.2)
  have hsIP : s ∉ polygonInterior P := fun hh => (hPI hh).1 hsB
  have hsOP : s ∈ polygonExterior P :=
    (show s ∈ polygonInterior P ∪ polygonExterior P from hcover.symm ▸ hsPB).resolve_left hsIP
  have hsclosed : s ∉ closure (polygonInterior P) := by
    rwa [hP.polygonExterior_eq_compl_closure_interior hdim] at hsOP
  by_contra hmiss
  have hSregions : S ⊆ polygonInterior P ∪ polygonExterior P := by
    rw [hcover]
    intro z hz hzP
    rcases hPB ▸ hzP with hzL | hzA
    · exact (hSI hz).1 (polygonCyclicPathBoundary_subset_boundary p a b hzL)
    · exact hmiss ⟨z, hz, hzA, fun he => (hSI hz).1 (hends he)⟩
  exact hsclosed (closure_mono
    (hS.subset_left_of_subset_union hIP hOP hdis hSregions ⟨x, hxS, hxP⟩) hsS)



theorem IsSimplePolygon.crosscut_intersects_continuous
    (hp : IsSimplePolygon p) (hq : IsSimplePolygonalArc q) (hdim : Module.finrank ℝ E = 2)
    (a b : Fin n) (hab : b ≠ a) (hfirst : q 0 = p a)
    (hlast : q (Fin.last (m + 1)) = p b)
    (hinside : polygonArcBoundary q \ {p a, p b} ⊆ polygonInterior p)
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 1)) (r s : E) (hf0 : f 0 = r) (hf1 : f 1 = s)
    (hfI : f '' Ioo 0 1 ⊆ polygonInterior p)
    (hr : r ∈ polygonCyclicPathBoundary p a b \ {p a, p b})
    (hs : s ∈ polygonCyclicPathBoundary p b a \ {p a, p b}) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f t ∈ polygonArcBoundary q \ {p a, p b} := by
  have hcl : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo (by norm_num)
  have hfc : ContinuousOn f (closure (Ioo (0 : ℝ) 1)) := hcl.symm ▸ hf
  have himage : f '' Icc (0 : ℝ) 1 ⊆ closure (f '' Ioo 0 1) := hcl ▸ hfc.image_closure
  have hrcl : r ∈ closure (f '' Ioo (0 : ℝ) 1) :=
    himage ⟨0, by constructor <;> norm_num, hf0⟩
  have hscl : s ∈ closure (f '' Ioo (0 : ℝ) 1) :=
    himage ⟨1, by constructor <;> norm_num, hf1⟩
  obtain ⟨x, ⟨t, ht, htx⟩, hx⟩ := hp.crosscut_intersects_preconnected hq hdim a b hab
    hfirst hlast hinside (f '' Ioo 0 1)
    (isPreconnected_Ioo.image f (hf.mono Ioo_subset_Icc_self)) hfI r s hr hs hrcl hscl
  exact ⟨t, ht, htx.symm ▸ hx⟩



theorem IsSimplePolygon.crosscut_intersects_continuous_of_cyclic_order
    (hp : IsSimplePolygon p) (hq : IsSimplePolygonalArc q) (hdim : Module.finrank ℝ E = 2)
    (a b c d : Fin n) (hfirst : q 0 = p a) (hlast : q (Fin.last (m + 1)) = p b)
    (hinside : polygonArcBoundary q \ {p a, p b} ⊆ polygonInterior p)
    (f : ℝ → E) (hf : ContinuousOn f (Icc 0 1)) (hf0 : f 0 = p c) (hf1 : f 1 = p d)
    (hfI : f '' Ioo 0 1 ⊆ polygonInterior p)
    (hac : 0 < cyclicDistance a c) (hcb : cyclicDistance a c < cyclicDistance a b)
    (hbd : cyclicDistance a b < cyclicDistance a d) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f t ∈ polygonArcBoundary q \ {p a, p b} := by
  have hab : b ≠ a := by
    intro hh
    rw [hh, cyclicDistance_self] at hcb
    omega
  have hcends : p c ∉ ({p a, p b} : Set E) := by
    rintro (hh | hh)
    · have hca := hp.vertices_injective hh
      rw [hca, cyclicDistance_self] at hac
      omega
    · have hce := hp.vertices_injective hh
      rw [hce] at hcb
      omega
  have hdends : p d ∉ ({p a, p b} : Set E) := by
    rintro (hh | hh)
    · have hda := hp.vertices_injective hh
      rw [hda, cyclicDistance_self] at hbd
      omega
    · have hdb := hp.vertices_injective hh
      rw [hdb] at hbd
      omega
  have hreverse : cyclicDistance b d < cyclicDistance b a := by
    rw [cyclicDistance_change_start a b d, if_neg (by omega)]
    have hsum := cyclicDistance_add_reverse a b hab
    have hdlt := cyclicDistance_lt a d
    omega
  exact hp.crosscut_intersects_continuous hq hdim a b hab hfirst hlast hinside
    f hf (p c) (p d) hf0 hf1 hfI
    ⟨(hp.vertex_mem_polygonCyclicPathBoundary_iff a b hab c).mpr hcb.le, hcends⟩
    ⟨(hp.vertex_mem_polygonCyclicPathBoundary_iff b a hab.symm d).mpr hreverse.le, hdends⟩

end PoincareConjecture.M25.Topology3D
