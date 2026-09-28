import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.ComponentComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.BoundaryAgreement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.PairedDisks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ChartSymmetry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Q₁" => Set.ofPred (fun x : P2 => depth 8 x = 1)
local notation "Rim" => Q₀ ∪ Q₁

theorem exists_circle_reduction_of_paired_components
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgproper : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (C : SurfaceIntersectionComponents Ann Ann f g Rim)
    (D : SurfaceIntersectionComponents Ann Ann g f Rim)
    (a b : P2)
    (hfirst_g : (Ann ∩ g ⁻¹' (f '' Ann)) ∩ Q₀ = {a})
    (hfirst_f : (Ann ∩ f ⁻¹' (g '' Ann)) ∩ Q₀ = {b})
    (hcircle : ∃ i, Disjoint (C.pieces i) Rim)
    (hcharts : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧
      IsEmbedding (fun x : Ann => k x) ∧ MapsTo k Ann R ∧
      EqOn k f (frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      (∀ x ∈ Ann ∩ k ⁻¹' (g '' Ann), k x = f x) ∧
      Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) <
        Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) ∧
      (∃ W : Set X, IsOpen W ∧ frontier R ⊆ W ∧
        ∀ z ∈ W, z ∈ k '' Ann ↔ z ∈ f '' Ann) ∧
      ∀ (y : X) (boundary : Bool), y ∈ (g '' Ann) ∩ (k '' Ann) →
        OriginalSurfacePairChart e (g '' Ann) (f '' Ann) y boundary →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) y boundary) := by
  classical
  have hrims : ∀ x ∈ Ann, ∀ y ∈ Ann, f x = g y → (x ∈ Rim ↔ y ∈ Rim) := by
    intro x hx y hy hxy
    change (depth 8 x = -1 ∨ depth 8 x = 1) ↔ (depth 8 y = -1 ∨ depth 8 y = 1)
    rw [← mem_frontier_planar_annulus_iff,← mem_frontier_planar_annulus_iff,
      ← hfproper x hx,← hgproper y hy,hxy]
  obtain ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,hPball,hQball,hPin,hQin,himage,
    _,havoid⟩ := exists_paired_circle_disks_of_one_marked_intersection
      C D hrims a b hfirst_g hfirst_f hcircle
  have hPinside : closure P.inside ⊆ interior Ann := by
    rw [interior_squareAnnulus (by norm_num : 2 * (1 : ℝ) < 8)]
    exact hPin
  have hQinside : closure Q.inside ⊆ interior Ann := by
    rw [interior_squareAnnulus (by norm_num : 2 * (1 : ℝ) < 8)]
    exact hQin
  have hQC : IsCompact (Q.boundary ℝ) := hQb.symm ▸ (D.topology j).1
  have hPC : IsCompact (P.boundary ℝ) := hPb.symm ▸ (C.topology i).1
  have hQconn : IsConnected (Q.boundary ℝ) := hQb.symm ▸ (D.topology j).2.1
  have hQregion : MapsTo f (Q.boundary ℝ) (interior R) := by
    intro x hx
    have hxin := hQinside (hQball.1 hx)
    rw [← self_sdiff_frontier]
    exact ⟨hfR (interior_subset hxin),fun hh =>
      ((hfproper x (interior_subset hxin)).mp hh).2 hxin⟩
  have hrestQ : IsClosed ((Ann ∩ f ⁻¹' (g '' Ann)) \ Q.boundary ℝ) := by
    rw [hQb]
    exact D.isClosed_complement_piece j
  have hrestP : IsClosed ((Ann ∩ g ⁻¹' (f '' Ann)) \ P.boundary ℝ) := by
    rw [hPb]
    exact C.isClosed_complement_piece i
  have hselectedCharts (x : P2) (hx : x ∈ Q.boundary ℝ) :
      Nonempty (OriginalSurfacePairChart e (f '' Ann) (g '' Ann) (f x) false) := by
    have hxin := hQinside (hQball.1 hx)
    obtain ⟨y,hy,hyx⟩ := himage.symm.subset ⟨x,hx,rfl⟩
    obtain ⟨H⟩ := hcharts x ⟨interior_subset hxin,
      fun hh => hh.2 hxin⟩ ⟨y,interior_subset (hPinside (hPball.1 hy)),hyx⟩
    exact ⟨H.swap⟩
  obtain ⟨T⟩ := nonempty_synchronizedCircleCollars he isCompact_planar_annulus
    isCompact_planar_annulus hf hg hfi hgi hfR hgR hQC hPC hQconn
    (hQball.1.trans hQinside) (hPball.1.trans hPinside) himage.symm hQregion
    hrestQ hrestP hselectedCharts (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨houter₀,houter₁,hinner⟩ := T.disk_containment Q P hQ hQi hP hPi
    rfl rfl hQinside hPinside havoid
  have hginner : MapsTo g (closure T.collar₁.inner.inside) (interior R) := by
    intro x hx
    have hxin := houter₁ (subset_closure (T.collar₁.nested hx))
    rw [← self_sdiff_frontier]
    exact ⟨hgR (interior_subset hxin),fun hh =>
      ((hgproper x (interior_subset hxin)).mp hh).2 hxin⟩
  obtain ⟨J,hJ,hJs⟩ := exists_planar_annulus_complex
  let := D.components_finite
  have hcover : ⋃ i, D.pieces i = J.space ∩ f ⁻¹' (g '' Ann) := by
    rw [hJs]
    exact D.cover.symm.trans D.right_space
  obtain ⟨k,hk,hki,hkR,hkeep,hfront,hproper,hsource,hcount,hcross⟩ :=
    exists_original_circle_reduction hR he J hJ T.depth_pos T.width_small T.collar₀
      T.collar₁ f g isCompact_planar_annulus (hJs.symm ▸ hf) hg (hJs.symm ▸ hfi) hgi
      (hJs.symm ▸ hfR) (by simpa only [hJs] using hfproper)
      (by simpa only [hJs] using houter₀) (houter₁.trans interior_subset) hginner
      T.tube T.tube_PL T.tube_interior T.tube_fibers (hJs.symm ▸ hinner)
      T.whole₁ (hJs.symm ▸ T.whole₀) T.period₀ T.period₁ D.pieces
      (fun i => (D.topology i).1.isClosed) D.disjoint hcover (fun i => (D.topology i).2.1)
  rw [hJs] at hk hki hkR hkeep hfront hproper hsource hcount hcross
  have hagree := exists_open_boundary_agreement_of_interior_modification
    (T.collar₀.outer.isFinitePLBallPair_closed_inside
      T.collar₀.outer_simplicial T.collar₀.outer_injective).isCompact houter₀
    (subset_closure : T.collar₀.outer.inside ⊆ closure T.collar₀.outer.inside)
    hf.continuousOn hk.continuousOn hfproper hproper hkeep
  refine ⟨k,hk,hki,hkR,hfront,hproper,?_,?_,hcount,hagree,hcross⟩
  · rw [hsource]
    exact sdiff_subset
  · intro x hx
    have hh := hsource.subset hx
    exact hkeep ⟨hh.1.1,hh.2⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
