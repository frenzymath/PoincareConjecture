import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Local
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Count.ClosedDeletion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_boundary_replacement_with_count_decrease
    {X ι E κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {A : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {N C qN qC W : Set E} (hN : IsFinitePLBallPair P2 N qN)
    (hC : IsFinitePLBallPair P2 C qC) (hNJ : N ⊆ J.space)
    (hcover : J.space ⊆ N ∪ C) (hseam : N ∩ C = W)
    {f g : E → X} (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    (hg : PolyhedralPLInCharts e g N) (hgi : InjOn g N) (hfix : EqOn g f W)
    (htrace : ∀ x ∈ N, g x ∈ f '' J.space ↔ x ∈ W) (havoid : Disjoint (g '' N) A)
    (pieces : κ → Set E) (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i, pieces i = J.space ∩ f ⁻¹' A) (hconn : ∀ i, IsConnected (pieces i))
    (hremoved : ((J.space ∩ f ⁻¹' A) \ C).Nonempty) :
    ∃ k : E → X, PolyhedralPLInCharts e k J.space ∧ InjOn k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧
      EqOn k g N ∧ EqOn k f (J.space ∩ C) ∧
      k '' J.space = (g '' N) ∪ (f '' (J.space ∩ C)) ∧
      J.space ∩ k ⁻¹' A = (J.space ∩ f ⁻¹' A) ∩ C ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' A : Set E)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' A : Set E)) := by
  have hNcopy := hN
  have hCcopy := hC
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKN, _⟩, _⟩, _⟩ := hNcopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLC, _⟩, _⟩, _⟩ := hCcopy
  obtain ⟨M, hM, hMs⟩ := J.exists_finite_triangulation_inter L hJ hL
  rw [hLC] at hMs
  have hwhole : N ∪ (J.space ∩ C) = J.space := by
    apply Subset.antisymm (union_subset hNJ inter_subset_left)
    intro x hx
    rcases hcover hx with hn | hc
    · exact Or.inl hn
    · exact Or.inr ⟨hx, hc⟩
  have hcommon : N ∩ (J.space ∩ C) = W := by
    rw [← hseam]
    ext x
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hNJ h.1, h.2⟩⟩
  have hgK : PolyhedralPLInCharts e g K.space := hKN.symm ▸ hg
  have hfM : PolyhedralPLInCharts e f M.space :=
    hf.restrict_finite M hM (hMs.subset.trans inter_subset_left)
  obtain ⟨k, hk, hkN, hkC⟩ := _root_.Dehn.exists_circle_attachment_map_union he K M hK hM
    hgK hfM (fun x hx hy ↦ hfix (hcommon.subset ⟨hKN.subset hx, hMs.subset hy⟩))
  have hkN' : EqOn k g N := hKN ▸ hkN
  have hkC' : EqOn k f (J.space ∩ C) := hMs ▸ hkC
  have hkJ : PolyhedralPLInCharts e k J.space := by
    simpa only [hKN, hMs, hwhole] using hk
  have hcross (x y : E) (hx : x ∈ N) (hy : y ∈ J.space ∩ C) (hxy : k x = k y) : x = y := by
    have hgxy : g x = f y := (hkN' hx).symm.trans (hxy.trans (hkC' hy))
    have hxW : x ∈ W := (htrace x hx).mp ⟨y, hy.1, hgxy.symm⟩
    exact hfi (hNJ hx) hy.1 ((hfix hxW).symm.trans hgxy)
  have hki : InjOn k J.space := by
    intro x hx y hy hxy
    rcases hwhole.superset hx with hx | hx <;> rcases hwhole.superset hy with hy | hy
    · exact hgi hx hy ((hkN' hx).symm.trans (hxy.trans (hkN' hy)))
    · exact hcross x y hx hy hxy
    · exact (hcross y x hy hx hxy.symm).symm
    · exact hfi hx.1 hy.1 ((hkC' hx).symm.trans (hxy.trans (hkC' hy)))
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp (J.isCompact_space_of_finite hJ)
  have hke : IsEmbedding (fun x : J.space ↦ k x) :=
    (hkJ.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy ↦ Subtype.ext (hki x.property y.property hxy))).isEmbedding
  have hsource : J.space ∩ k ⁻¹' A = (J.space ∩ f ⁻¹' A) ∩ C := by
    ext x
    constructor
    · intro hx
      have hxNotN : x ∉ N := fun hn ↦ Set.disjoint_left.mp havoid
        ⟨x, hn, (hkN' hn).symm⟩ hx.2
      have hxC := (hcover hx.1).resolve_left hxNotN
      refine ⟨⟨hx.1, ?_⟩, hxC⟩
      change f x ∈ A
      rw [← hkC' ⟨hx.1, hxC⟩]
      exact hx.2
    · intro hx
      refine ⟨hx.1.1, ?_⟩
      change k x ∈ A
      rw [hkC' ⟨hx.1.1, hx.2⟩]
      exact hx.1.2
  have hboundary : Disjoint (J.space ∩ f ⁻¹' A) (N ∩ C) := by
    apply Set.disjoint_left.mpr
    intro x hx hxNC
    exact Set.disjoint_left.mp havoid ⟨x, hxNC.1, hfix (hseam.subset hxNC)⟩ hx.2
  refine ⟨k, hkJ, hki, hke, hkN', hkC', ?_, hsource, ?_⟩
  · conv_lhs => rw [← hwhole, image_union, image_congr hkN', image_congr hkC']
  · rw [hsource]
    exact connectedComponents_card_lt_of_closed_cut_deletion pieces hclosed hdis hpieces hconn
      hN.isCompact.isClosed hC.isCompact.isClosed (inter_subset_left.trans hcover) hboundary hremoved

end PoincareConjecture.M76.Dehn.Annuli
