import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalFaceEdgeGapFamily

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem original_face_cut_mem_iff
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) {T : Set E} {S : Set X}
    (hsub : T ⊆ convexHull ℝ (s : Set E))
    (hphysical : g '' T = S ∩ (g '' convexHull ℝ (s : Set E)))
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) : x ∈ T ↔ g x ∈ S := by
  constructor
  · exact fun hxT => (hphysical.subset (mem_image_of_mem g hxT)).1
  · intro hxS
    obtain ⟨y,hy,hyx⟩ := hphysical.symm.subset ⟨hxS,mem_image_of_mem g hx⟩
    have he := hgi (K.convexHull_subset_space hs (hsub hy)) (K.convexHull_subset_space hs hx) hyx
    exact he ▸ hy

theorem original_face_edge_gap_to_physical_cut
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) {T : Set E} {S : Set X}
    (hsub : T ⊆ convexHull ℝ (s : Set E))
    (hphysical : g '' T = S ∩ (g '' convexHull ℝ (s : Set E)))
    (e : ℝ →ᴬ[ℝ] E) (hes : ({e 0,e 1} : Finset E) ⊆ s)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (ha : e a ∈ T) (hb : e b ∈ T) (hgap : Disjoint (e '' Ioo a b) T) :
    e a ∈ g ⁻¹' S ∧ e b ∈ g ⁻¹' S ∧ Disjoint (e '' Ioo a b) (g ⁻¹' S) := by
  have hmaps : e '' Icc (0 : ℝ) 1 ⊆ convexHull ℝ (s : Set E) := by
    rw [affine_unit_interval_image]
    apply convexHull_mono
    simpa only [Finset.coe_insert,Finset.coe_singleton] using
      (show (({e 0,e 1} : Finset E) : Set E) ⊆ (s : Set E) from hes)
  refine ⟨(hphysical.subset (mem_image_of_mem g ha)).1,
    (hphysical.subset (mem_image_of_mem g hb)).1,disjoint_left.mpr ?_⟩
  rintro x ⟨t,ht,rfl⟩ htS
  have htface : e t ∈ convexHull ℝ (s : Set E) :=
    hmaps (mem_image_of_mem e ⟨ha0.trans ht.1.le,ht.2.le.trans hb1⟩)
  have htT := (original_face_cut_mem_iff K g hgi hs hsub hphysical htface).mpr htS
  exact disjoint_left.mp hgap (mem_image_of_mem e ht) htT

theorem original_physical_face_edge_gaps_match
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s u : Finset E} (hs : s ∈ K.faces) (hu : u ∈ K.faces)
    {T V : Set E} {S : Set X}
    (hT : T ⊆ convexHull ℝ (s : Set E)) (hV : V ⊆ convexHull ℝ (u : Set E))
    (hphysicalT : g '' T = S ∩ (g '' convexHull ℝ (s : Set E)))
    (hphysicalV : g '' V = S ∩ (g '' convexHull ℝ (u : Set E)))
    (e f : ℝ →ᴬ[ℝ] E) (he : Function.Injective e) (hf : Function.Injective f)
    (heK : ({e 0,e 1} : Finset E) ∈ K.faces)
    (hfK : ({f 0,f 1} : Finset E) ∈ K.faces)
    (hes : ({e 0,e 1} : Finset E) ⊆ s) (hfu : ({f 0,f 1} : Finset E) ⊆ u)
    {a b c d : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hd1 : d ≤ 1)
    (ha : e a ∈ T) (hb : e b ∈ T) (hc : f c ∈ V) (hd : f d ∈ V)
    (hab : Disjoint (e '' Ioo a b) T) (hcd : Disjoint (f '' Ioo c d) V)
    (hmeet : ((e '' Ioo a b) ∩ (f '' Ioo c d)).Nonempty) :
    ({e 0,e 1} : Finset E) = {f 0,f 1} ∧
      e '' Icc a b = f '' Icc c d ∧ g '' (e '' Icc a b) = g '' (f '' Icc c d) := by
  obtain ⟨ha',hb',hab'⟩ := original_face_edge_gap_to_physical_cut K g hgi hs hT hphysicalT
    e hes ha0 hb1 ha hb hab
  obtain ⟨hc',hd',hcd'⟩ := original_face_edge_gap_to_physical_cut K g hgi hu hV hphysicalV
    f hfu hc0 hd1 hc hd hcd
  obtain ⟨hedge,hside⟩ := original_simplicial_edge_gaps_match K e f he hf heK hfK
    ha0 hb1 hc0 hd1 ha' hb' hc' hd' hab' hcd' hmeet
  exact ⟨hedge,hside,congrArg (fun A => g '' A) hside⟩

end PoincareConjecture.M76.PrismBelt
