import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.PairedSelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Construction



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_returning_reduction_of_paired_components
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (hF : F ⊆ frontier R) (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    {H T : Set P2} (hH : IsFinitePLBallPair P2 H (frontier H))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hHT : H ⊆ interior T)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hJs : J.space = T \ interior H)
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g J.space)
    (hfi : InjOn f J.space) (hgi : InjOn g J.space)
    (hfR : MapsTo f J.space R) (hgR : MapsTo g J.space R)
    (hfp : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H)
    (hgp : ∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H)
    (hfmark : MapsTo f (J.space ∩ frontier T) F)
    (hgmark : MapsTo g (J.space ∩ frontier T) F)
    (hprotected : ∀ x ∈ J.space, ∀ y ∈ J.space, f x = g y →
      (x ∈ frontier H ↔ y ∈ frontier H))
    (C : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) f g
      (frontier H ∪ frontier T))
    (D : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) g f
      (frontier H ∪ frontier T))
    (a : P2) (hfirst : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H))) ∩ frontier H = {a})
    (hmeet : ∀ x : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
      ∃ y : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier H ∪ frontier T)
    (hreturn : ∃ i, Disjoint (C.pieces i) (frontier H))
    (hboundary : ∀ x ∈ J.space, f x ∈ g '' J.space → f x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ J.space, f x ∈ g '' J.space → f x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (f x) false)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧ MapsTo k J.space R ∧
      EqOn k f (J.space ∩ frontier H) ∧ MapsTo k (J.space ∩ frontier T) F ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H) ∧
      J.space ∩ k ⁻¹' (g '' J.space) ⊆ J.space ∩ f ⁻¹' (g '' J.space) ∧
      EqOn k f (J.space ∩ k ⁻¹' (g '' J.space)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (g '' J.space) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' (g '' J.space) : Set P2)) ∧
      (∀ x ∈ J.space, k x ∈ g '' J.space → k x ∈ frontier R →
        ∃ B : OriginalSurfacePairChart e (k '' J.space) (g '' J.space) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      ∀ x ∈ J.space, k x ∈ g '' J.space → k x ∈ interior R →
        Nonempty (OriginalSurfacePairChart e (k '' J.space) (g '' J.space) (k x) false) := by
  classical
  let := D.components_finite
  have hrims : ∀ x ∈ T \ interior H, ∀ y ∈ T \ interior H, f x = g y →
      (x ∈ frontier H ∪ frontier T ↔ y ∈ frontier H ∪ frontier T) := by
    intro x hx y hy hxy
    rw [union_comm (frontier H), ← hfp x (hJs.superset hx), ← hgp y (hJs.superset hy), hxy]
  obtain ⟨i, j, D₀, E₀, U₀, V₀, D₁, E₁, U₁, V₁, hD₀, hE₀, hU₀, hcover₀,
    hcommon₀, hDU₀, hEV₀, hD₀H, hD₀T, hD₁, hE₁, hcover₁, hcommon₁, hDU₁,
    hD₁H, hD₁T, hball, himage, honly, hrest⟩ :=
    exists_paired_returning_cut_disks hH hT hHT C D hrims
      (fun x hx y hy hxy ↦ hprotected x (hJs.superset hx) y (hJs.superset hy) hxy)
      a hfirst hmeet hreturn
  have hdisRims : Disjoint (frontier T) (frontier H) := by
    refine disjoint_left.mpr fun x hxT hxH ↦ ?_
    exact hxT.2 (hHT (hH.1 hxH))
  have hrim : frontier T ∪ frontier H ⊆ J.space := by
    intro x hx
    apply hJs.superset
    rcases hx with ht | hh
    · exact ⟨hT.1 ht, fun hi ↦ ht.2 (hHT (interior_subset hi))⟩
    · exact ⟨interior_subset (hHT (hH.1 hh)), hh.2⟩
  have hD₀S : D₀ ⊆ J.space := fun x hx ↦ hJs.superset
    ⟨(hD₀T hx).1, fun hi ↦ (hD₀T hx).2 (interior_subset hi)⟩
  have hD₁S : D₁ ⊆ J.space := fun x hx ↦ hJs.superset
    ⟨(hD₁T hx).1, fun hi ↦ (hD₁T hx).2 (interior_subset hi)⟩
  have hpieces : (⋃ j, D.pieces j) = J.space ∩ f ⁻¹' (g '' J.space) := by
    rw [hJs]
    exact D.cover.symm.trans D.right_space
  have hrest' : IsClosed ((J.space ∩ f ⁻¹' (g '' J.space)) \ D.pieces j) := by
    simpa only [hJs] using hrest
  obtain ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hksub, hkkeep, hkcount, hkb, hki', _⟩ :=
    exists_original_returning_arc_removal_of_cut_disks hR he hF hFopen J J hJ hJ hT
      isClosed_frontier isClosed_frontier hdisRims isClosed_frontier isClosed_frontier hdisRims
      hrim hrim hD₀ hE₀ hU₀ hDU₀ hEV₀ hcover₀ hcommon₀ hD₁ hE₁ hDU₁
      ((hJs.subset.trans sdiff_subset).trans hcover₁.symm.subset) hcommon₁
      (hJs.subset.trans sdiff_subset) hD₀S hD₁S
      (hD₀H.mono_right hH.1) (hD₁H.mono_right hH.1) hball hf hg hfi hgi hfR hgR
      hfp hgp hfmark hgmark himage
      (fun x hx hfg ↦ honly x hx (by simpa only [hJs] using hfg)) hrest' hboundary hinterior
      D.pieces (fun j ↦ (D.topology j).1.isClosed) D.disjoint hpieces (fun j ↦ (D.topology j).2.1)
  exact ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hksub, hkkeep, hkcount, hkb, hki'⟩

end PoincareConjecture.M76.Dehn.Annuli
