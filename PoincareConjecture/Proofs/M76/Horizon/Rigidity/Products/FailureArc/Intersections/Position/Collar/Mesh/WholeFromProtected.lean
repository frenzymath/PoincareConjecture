import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.CollarPosition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.SubdivisionGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusCarrier



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_whole_planar_position_from_protected_collar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (Source N L : SimplicialComplex ℝ V2)
    (hSource : Source.faces.Finite) (hN : N.faces.Finite) (hLN : L ≤ N)
    (hNs : N.space = Ann)
    {f g : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hfi : InjOn f Source.space) (hg : PolyhedralPLInCharts e g N.space)
    (hgi : InjOn g N.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hrim : ∀ x ∈ Source.space, x ∉ interior Source.space → f x ∈ frontier R)
    (hproper : ∀ x ∈ N.space, g x ∈ frontier R ↔ x ∈ frontier Ann)
    {c : ℝ} (hc : 0 ≤ c)
    (hLs : L.space = N.space ∩ {x | planarAnnulusRimHeight x ≤ c})
    (hvertices : Disjoint (f '' Source.space) (g '' (N.vertices ∩ L.space)))
    (hstars : ∀ p ∈ N.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (N.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (N.closedStar p).AffineOnFaces (B ∘ g))
    (hactive : ∀ s ∈ N.faces, s ∉ L.faces →
      ∃ (B : OpenPartialHomeomorph X V3) (A : V2 →ᴬ[ℝ] V3),
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        Disjoint B.source (frontier R) ∧ MapsTo g (convexHull ℝ (s : Set V2)) B.source ∧
        EqOn (B ∘ g) A (convexHull ℝ (s : Set V2)))
    (hcut : ∀ a ∈ N.faces, a.card = 2 →
      convexHull ℝ (a : Set V2) ⊆ {x | x ∈ N.space ∧ planarAnnulusRimHeight x = c} →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set V2))).Finite ∧
        HasOriginalEdgeCofaceCharts e (f '' Source.space) N g a)
    (hboundary : ∀ x ∈ N.space \ interior N.space, g x ∈ f '' Source.space →
      ∃ C : OriginalSurfacePairChart e (f '' Source.space) (g '' N.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hcollar : ∀ x ∈ L.space, x ∈ interior N.space → g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' N.space) (g x) false)) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ EqOn F id W ∧ g '' L.space ⊆ W ∧ EqOn F id (frontier R) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧ InjOn (F ∘ f) Source.space ∧
      (∀ x ∈ Source.space, x ∉ interior Source.space → F (f x) = f x) ∧
      (∀ x ∈ N.space \ interior N.space, g x ∈ (F ∘ f) '' Source.space →
        ∃ C : OriginalSurfacePairChart e ((F ∘ f) '' Source.space) (g '' N.space) (g x) true,
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      (∀ x ∈ interior N.space, g x ∈ (F ∘ f) '' Source.space →
        Nonempty (OriginalSurfacePairChart e ((F ∘ f) '' Source.space)
          (g '' N.space) (g x) false)) ∧
      Nonempty (SurfaceIntersectionComponents Source.space N.space (F ∘ f) g
        (N.space \ interior N.space)) := by
  classical
  have hL : L.faces.Finite := hN.subset hLN
  have hLclosed : IsClosed (g '' L.space) :=
    ((L.isCompact_space_of_finite hL).image_of_continuousOn
      (hg.continuousOn.mono (fun x hx => by
        obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
        exact N.convexHull_subset_space (hLN hs) hxs))).isClosed
  have hboundL : N.space \ interior N.space ⊆ L.space := by
    intro x hx
    have hxfront : x ∈ frontier Ann := by
      rw [← hNs, (N.isCompact_space_of_finite hN).isClosed.frontier_eq]
      exact hx
    refine hLs.symm.subset ⟨hx.1, ?_⟩
    change planarAnnulusRimHeight x ≤ c
    rw [(planarAnnulusRimHeight_eq_zero_iff (hNs.subset hx.1)).mpr hxfront]
    exact hc
  let Z := g '' L.space ∪ frontier R
  have hZ : IsClosed Z := hLclosed.union isClosed_frontier
  have hmark : ∀ x ∈ N.space, g x ∈ Z ↔ x ∈ L.space := by
    intro x hx
    constructor
    · rintro (⟨y, hy, hyx⟩ | hxfront)
      · have hyN := (hLs.subset hy).1
        exact hgi hyN hx hyx ▸ hy
      · have hxfront' := (hproper x hx).mp hxfront
        refine hLs.symm.subset ⟨hx, ?_⟩
        change planarAnnulusRimHeight x ≤ c
        rw [(planarAnnulusRimHeight_eq_zero_iff (hNs.subset hx)).mpr hxfront']
        exact hc
    · exact fun hxL => Or.inl (mem_image_of_mem g hxL)
  have hprotectedV : Disjoint (f '' Source.space ∩ Z) (g '' N.vertices) := by
    apply disjoint_left.mpr
    rintro y ⟨hyS, hyZ⟩ ⟨x, hxV, rfl⟩
    exact disjoint_left.mp hvertices hyS
      ⟨x, ⟨hxV, (hmark x (N.vertices_subset_space hxV)).mp hyZ⟩, rfl⟩
  let : Finite (N.FaceOfCard 3) := N.finite_faceOfCard hN 3
  let : Fintype (N.FaceOfCard 3) := Fintype.ofFinite _
  let faces := Finset.univ.filter (fun s : N.FaceOfCard 3 => s.1 ∉ L.faces)
  have hmem (s : N.FaceOfCard 3) : s ∈ faces ↔ s.1 ∉ L.faces := by simp [faces]
  choose B A hB hBmark hmap hA using
    fun s : {s : N.FaceOfCard 3 // s.1 ∉ L.faces} => hactive s.1.1 s.1.2.1 s.2
  let B' (s : N.FaceOfCard 3) := if hs : s.1 ∉ L.faces then B ⟨s, hs⟩ else e (hcover (g 0)).choose
  let A' (s : N.FaceOfCard 3) := if hs : s.1 ∉ L.faces then A ⟨s, hs⟩ else 0
  have hedge : ∀ a ∈ L.faces, a.card = 2 → (∃ s ∈ faces, a ⊆ s.1) →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set V2))).Finite ∧
        HasOriginalEdgeCofaceCharts e (f '' Source.space) N g a := by
    intro a ha ha2 hface
    obtain ⟨s, hs, has⟩ := hface
    exact hcut a (hLN ha) ha2 (protected_active_edge_subset_cut N L hLN
      continuous_planarAnnulusRimHeight hLs ha s.2.1 ((hmem s).mp hs) has)
  obtain ⟨F, W, hW, hfix, hLW, hFfront, hFPL, hFinv, hfF, hFi, hrimF, _, hintF, hcomponents⟩ :=
    exists_collar_protected_whole_planar_position Source hSource hf hfi hcover he N L hN hLN
      g hg.continuousOn hgi hg hstars hZ hmark hprotectedV faces hedge subset_union_right hrim
      (fun s hs => (hmem s).mp hs) (fun s hs => (hmem s).mpr hs) B'
      (by intro s hs; simpa only [B', dif_pos ((hmem s).mp hs)] using hB ⟨s, (hmem s).mp hs⟩)
      (by intro s hs; simpa only [B', dif_pos ((hmem s).mp hs)] using hBmark ⟨s, (hmem s).mp hs⟩)
      A'
      (by intro s hs; simpa only [B', dif_pos ((hmem s).mp hs)] using hmap ⟨s, (hmem s).mp hs⟩)
      (by intro s hs; simpa only [B', A', dif_pos ((hmem s).mp hs)] using hA ⟨s, (hmem s).mp hs⟩)
      hboundL (fun x hx hxf => ⟨(hboundary x hx hxf).choose⟩) hcollar
  refine ⟨F, W, hW, hfix, hLW, hFfront, hFPL, hFinv, hfF, hFi, hrimF, ?_, hintF, hcomponents⟩
  intro x hx hxf
  have hxW := hLW (mem_image_of_mem g (hboundL hx))
  have himage : (F ∘ f) '' Source.space = F '' (f '' Source.space) :=
    (image_image F f Source.space).symm
  have hxold : g x ∈ f '' Source.space := by
    rw [himage] at hxf
    obtain ⟨y, hy, hyx⟩ := hxf
    exact F.injective (hyx.trans (hfix hxW).symm) ▸ hy
  obtain ⟨C, hC⟩ := hboundary x hx hxold
  rw [himage]
  refine ⟨C.image_first_of_fixed_neighborhood F hW hxW hfix, ?_⟩
  intro z hz
  exact hC z hz.1

end PoincareConjecture.M76
