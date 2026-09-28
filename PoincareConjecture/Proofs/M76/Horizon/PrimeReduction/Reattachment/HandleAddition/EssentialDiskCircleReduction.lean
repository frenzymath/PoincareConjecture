import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskCirclePair

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76
open Dehn.Annuli.CircleResolution
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_disk_contact_reduction_of_inessential_surface_circle
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hJcv : Convex ℝ J.space)
    {K B : Set P2} (hK : IsCompact K) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g K)
    (hfi : InjOn f J.space) (hgi : InjOn g K)
    (hfR : MapsTo f J.space R) (hgR : MapsTo g K R)
    (hfproper : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hgproper : ∀ x ∈ K, g x ∈ frontier R ↔ x ∈ B)
    (C : SurfaceIntersectionComponents J.space K f g B)
    (D : SurfaceIntersectionComponents K J.space g f (frontier J.space))
    (hgood : ∃ i, ∃ (n : ℕ) (P : Polygon P2 (n+3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
      P.boundary ℝ = C.pieces i ∧ closure P.inside ⊆ interior K \ B)
    (hcharts : ∀ x ∈ J.space \ frontier J.space, f x ∈ g '' K →
      Nonempty (OriginalSurfacePairChart e (g '' K) (f '' J.space) (f x) false)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space => k x) ∧ MapsTo k J.space R ∧
      EqOn k f (frontier J.space) ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      J.space ∩ k ⁻¹' (g '' K) ⊆ J.space ∩ f ⁻¹' (g '' K) ∧
      (∀ x ∈ J.space ∩ k ⁻¹' (g '' K), k x = f x) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (g '' K) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' (g '' K) : Set P2)) ∧
      (∃ W : Set X, IsOpen W ∧ frontier R ⊆ W ∧
        ∀ z ∈ W, z ∈ k '' J.space ↔ z ∈ f '' J.space) ∧
      ∀ (y : X) (boundary : Bool), y ∈ (g '' K) ∩ (k '' J.space) →
        OriginalSurfacePairChart e (g '' K) (f '' J.space) y boundary →
        Nonempty (OriginalSurfacePairChart e (g '' K) (k '' J.space) y boundary) := by
  classical
  have hrims : ∀ x ∈ J.space, ∀ y ∈ K, f x = g y →
      (x ∈ frontier J.space ↔ y ∈ B) := by
    intro x hx y hy hxy
    rw [← hfproper x hx,← hgproper y hy,hxy]
  obtain ⟨i,j,n,m,P,Q,hPi,hP,hQi,hQ,hPb,hQb,hPball,hQball,hPin,hQin,himage,
    _,havoid⟩ := exists_paired_innermost_disk_of_region_contact hJcv C D hrims hgood
  have hPinside : closure P.inside ⊆ interior K := fun _ hx => (hPin hx).1
  have hQC : IsCompact (Q.boundary ℝ) := hQb.symm ▸ (D.topology j).1
  have hPC : IsCompact (P.boundary ℝ) := hPb.symm ▸ (C.topology i).1
  have hQconn : IsConnected (Q.boundary ℝ) := hQb.symm ▸ (D.topology j).2.1
  have hQregion : MapsTo f (Q.boundary ℝ) (interior R) := by
    intro x hx
    have hxin := hQin (hQball.1 hx)
    rw [← self_sdiff_frontier]
    exact ⟨hfR (interior_subset hxin),fun hh =>
      ((hfproper x (interior_subset hxin)).mp hh).2 hxin⟩
  have hrestQ : IsClosed ((J.space ∩ f ⁻¹' (g '' K)) \ Q.boundary ℝ) := by
    rw [hQb]
    exact D.isClosed_complement_piece j
  have hrestP : IsClosed ((K ∩ g ⁻¹' (f '' J.space)) \ P.boundary ℝ) := by
    rw [hPb]
    exact C.isClosed_complement_piece i
  have hselectedCharts (x : P2) (hx : x ∈ Q.boundary ℝ) :
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' K) (f x) false) := by
    have hxin := hQin (hQball.1 hx)
    obtain ⟨y,hy,hyx⟩ := himage.symm.subset ⟨x,hx,rfl⟩
    obtain ⟨H⟩ := hcharts x ⟨interior_subset hxin,
      fun hh => hh.2 hxin⟩ ⟨y,interior_subset (hPinside (hPball.1 hy)),hyx⟩
    exact ⟨H.swap⟩
  obtain ⟨T⟩ := nonempty_synchronizedCircleCollars he (J.isCompact_space_of_finite hJ)
    hK hf hg hfi hgi hfR hgR hQC hPC hQconn
    (hQball.1.trans hQin) (hPball.1.trans hPinside) himage.symm hQregion
    hrestQ hrestP hselectedCharts (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨houter₀,houter₁,hinner⟩ := T.disk_containment Q P hQ hQi hP hPi
    rfl rfl hQin hPinside havoid
  obtain ⟨hinnerP,_⟩ := oriented_collar_middle_disk T.depth_pos T.width_small
    T.collar₁ P hP hPi T.middle₁
  have hginner : MapsTo g (closure T.collar₁.inner.inside) (interior R) := by
    intro x hx
    have hxin := hPin (subset_closure (hinnerP hx))
    exact (mem_interior_iff_notMem_frontier (hgR (interior_subset hxin.1))).mpr
      (fun hh => hxin.2 ((hgproper x (interior_subset hxin.1)).mp hh))
  let := D.components_finite
  have hcover : ⋃ i, D.pieces i = J.space ∩ f ⁻¹' (g '' K) :=
    D.cover.symm.trans D.right_space
  obtain ⟨k,hk,hki,hkR,hkeep,hfront,hproper,hsource,hcount,hcross⟩ :=
    exists_original_circle_reduction hR he J hJ T.depth_pos T.width_small T.collar₀
      T.collar₁ f g hK hf hg hfi hgi hfR hfproper houter₀
      (houter₁.trans interior_subset) hginner
      T.tube T.tube_PL T.tube_interior T.tube_fibers hinner
      T.whole₁ T.whole₀ T.period₀ T.period₁ D.pieces
      (fun i => (D.topology i).1.isClosed) D.disjoint hcover (fun i => (D.topology i).2.1)
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

end PoincareConjecture.M76
