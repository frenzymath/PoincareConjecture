import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.MarkedAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Intersections.PlanarSpanningPair



set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus
open PoincareConjecture.M76.Dehn.Annuli
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q" => sphere (0 : V2) 1
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_original_positioned_planar_spanning_pair
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hdis : Disjoint (F false) (F true))
    (hcomponent : ∀ b y, y ∈ F b → connectedComponentIn (frontier R) y = F b)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (j : Bool → V1 × V2 → X)
    (hj : ∀ b, PolyhedralPLInCharts e (j b) source)
    (hji : ∀ b, InjOn (j b) source) (hjR : ∀ b, MapsTo (j b) source R)
    (hjp : ∀ b (x : source), j b x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1)
    (hjmark : ∀ b c (z : Q), j b (endpoint c, z) ∈ F c)
    (p : X) (hpoint : ((j false '' source) ∩ (j true '' source)) ∩ F false = {p})
    (hboundary : ∀ y ∈ (j false '' source) ∩ (j true '' source), y ∈ frontier R →
      ∃ C : OriginalSurfacePairChart e (j false '' source) (j true '' source) y true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    ∃ (f g : P2 → X) (q : X),
      PolyhedralPLInCharts e f Ann ∧ PolyhedralPLInCharts e g Ann ∧
      InjOn f Ann ∧ InjOn g Ann ∧ MapsTo f Ann R ∧ MapsTo g Ann R ∧
      (∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1) ∧
      (∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1) ∧
      MapsTo f (Ann ∩ Last) (F true) ∧ MapsTo g (Ann ∩ Last) (F true) ∧
      ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {q} ∧
      (∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
        ∃ C : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
          (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) ∧
      ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false) := by
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  have hcompact : IsCompact source := hKs ▸ K.isCompact_space_of_finite hK
  let : CompactSpace source := isCompact_iff_compactSpace.mp hcompact
  have hjemb (b : Bool) : IsEmbedding (fun x : source => j b x) :=
    ((continuousOn_iff_continuous_domRestrict.mp (hj b).continuousOn).isClosedEmbedding
      (fun x y hh => Subtype.ext (hji b x.property y.property hh))).isEmbedding
  obtain ⟨g, hg, hgi, hgR, hgp, hgm, hgu, himage, hp⟩ :=
    exists_planar_spanning_pair_with_marked_intersection F hF hdis j hj hjemb hjR hjp hjmark p hpoint
  have hproper (b : Bool) : ∀ x ∈ Ann, g b x ∈ frontier R ↔ x ∈ frontier Ann := by
    intro x hx
    exact (hgp b ⟨x, hx⟩).trans (mem_frontier_planar_annulus_iff x).symm
  have hboundaryG : ∀ x ∈ frontier Ann, g true x ∈ g false '' Ann →
      ∃ C : OriginalSurfacePairChart e (g false '' Ann) (g true '' Ann) (g true x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    intro x hx hxf
    have hxAnn := isCompact_planar_annulus.isClosed.frontier_subset hx
    rw [himage false, himage true]
    exact hboundary _ ⟨(himage false).subset hxf, (himage true).subset (mem_image_of_mem _ hxAnn)⟩
      ((hproper true x hxAnn).mpr hx)
  obtain ⟨k, q, hk, hki, hkR, hkp, hkm, hku, hq, hkb, hkiCharts⟩ :=
    exists_original_marked_position_of_boundary_charts F hcover he hF hcomponent
      (hg false) (hg true) (hgi false) (hgi true) (hgR false) (hgR true)
      (hproper false) (hproper true) (fun x hx => hgm false ⟨x, hx⟩)
      (fun x hx => hgu false ⟨x, hx.1⟩ hx.2) p hp hboundaryG
  exact ⟨k, g true, q, hk, hg true, hki, hgi true, hkR, hgR true, hkp, hproper true,
    hkm, (fun x hx => hgm true ⟨x, hx⟩), hku, (fun x hx => hgu true ⟨x, hx.1⟩ hx.2),
    hq, hkb, hkiCharts⟩

end PoincareConjecture.M76
