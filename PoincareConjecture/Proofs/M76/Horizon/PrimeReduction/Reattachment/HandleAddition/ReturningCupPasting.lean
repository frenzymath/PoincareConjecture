import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Local
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Count.ClosedDeletion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.ReturningDiskImageEssentiality
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Preservation



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_embedded_disk_paste
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {N C qN qC W : Set E} (hN : IsFinitePLBallPair P2 N qN)
    (hC : IsFinitePLBallPair P2 C qC) (hNJ : N ⊆ J.space)
    (hcover : J.space ⊆ N ∪ C) (hseam : N ∩ C = W)
    {f g : E → X} (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    (hg : PolyhedralPLInCharts e g N) (hgi : InjOn g N) (hfix : EqOn g f W)
    (htrace : ∀ x ∈ N, g x ∈ f '' J.space ↔ x ∈ W) :
    ∃ k : E → X, PolyhedralPLInCharts e k J.space ∧ InjOn k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧
      EqOn k g N ∧ EqOn k f (J.space ∩ C) ∧
      k '' J.space = (g '' N) ∪ (f '' (J.space ∩ C)) := by
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
  refine ⟨k,hkJ,hki,hke,hkN',hkC',?_⟩
  conv_lhs => rw [←hwhole,image_union,image_congr hkN',image_congr hkC']

theorem exists_essential_pasted_cup_contact_decrease
    {X ι E κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {A R : Set X}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {q N C qN qC W : Set E} (hDisk : IsFinitePLBallPair P2 J.space q)
    (hN : IsFinitePLBallPair P2 N qN) (hC : IsFinitePLBallPair P2 C qC)
    (hNJ : N ⊆ J.space) (hcover : J.space ⊆ N ∪ C) (hseam : N ∩ C = W)
    {f v g u : E → X} (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    (hfR : MapsTo f J.space R) (hfproper : ∀ x ∈ J.space,f x ∈ frontier R ↔ x ∈ q)
    (hv : PolyhedralPLInCharts e v N) (hvi : InjOn v N) (hvfix : EqOn v f W)
    (hvtrace : ∀ x ∈ N,v x ∈ f '' J.space ↔ x ∈ W)
    (hvR : MapsTo v N R) (hvproper : ∀ x ∈ N,v x ∈ frontier R ↔ x ∈ q)
    (hg : PolyhedralPLInCharts e g N) (hgi : InjOn g N) (hgfix : EqOn g f W)
    (hgtrace : ∀ x ∈ N,g x ∈ f '' J.space ↔ x ∈ W)
    (hgavoid : Disjoint (g '' N) A)
    (H : C(↥(Icc (0 : ℝ) 1) × ↥N,X))
    (hH0 : ∀ x : N,H (⟨0,by norm_num⟩,x) = v x)
    (hH1 : ∀ x : N,H (⟨1,by norm_num⟩,x) = g x)
    (hHR : ∀ z,H z ∈ R)
    (hHfront : ∀ z,H z ∈ frontier R ↔ v z.2 ∈ frontier R)
    (hHfix : ∀ z,(z.2:E) ∈ W → H z = v z.2)
    (hu : ContinuousOn u J.space) (huq : ∀ x ∈ q,u x ∈ frontier R)
    (hne : ¬∃ F : C(J.space,frontier R),∀ x : q,(F ⟨x,hDisk.1 x.property⟩:X) = u x)
    (Hcup : C(↥(Icc (0 : ℝ) 1) × ↥(v '' N ∪ f '' (J.space ∩ C)),X))
    (hcup1 : ∀ z : ↥(v '' N ∪ f '' (J.space ∩ C)),Hcup (⟨1,by norm_num⟩,z) = z)
    (hcupfront : ∀ z,Hcup z ∈ frontier R ↔ (z.2:X) ∈ frontier R)
    (hcupi : Function.Injective (fun z => Hcup (⟨0,by norm_num⟩,z)))
    (hcupimage : u '' J.space ⊆ Set.range (fun z => Hcup (⟨0,by norm_num⟩,z)))
    (pieces : κ → Set E) (hclosed : ∀ i,IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hpieces : ⋃ i,pieces i = J.space ∩ f ⁻¹' A) (hconn : ∀ i,IsConnected (pieces i))
    (hremoved : ((J.space ∩ f ⁻¹' A) \ C).Nonempty) :
    ∃ k : E → X,PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space => k x) ∧ MapsTo k J.space R ∧
      EqOn k f (J.space ∩ C) ∧
      (∀ x ∈ J.space,k x ∈ frontier R ↔ x ∈ q) ∧
      J.space ∩ k ⁻¹' A = (J.space ∩ f ⁻¹' A) ∩ C ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' A : Set E)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' A : Set E)) ∧
      (¬∃ F : C(J.space,frontier R),∀ x : q,(F ⟨x,hDisk.1 x.property⟩:X) = k x) ∧
      ∃ O : Set X,IsOpen O ∧ A ∩ (k '' J.space) ⊆ O ∧
        ∀ z ∈ O,z ∈ k '' J.space ↔ z ∈ f '' J.space := by
  obtain ⟨j,hj,hji,_,hjN,hjC,hjimage⟩ := exists_original_embedded_disk_paste he J hJ
    hN hC hNJ hcover hseam hf hfi hv hvi hvfix hvtrace
  have hjR : MapsTo j J.space R := by
    intro x hx
    rcases hcover hx with hn | hc
    · rw [hjN hn]; exact hvR hn
    · rw [hjC ⟨hx,hc⟩]; exact hfR hx
  have hjproper (x : E) (hx : x ∈ J.space) : j x ∈ frontier R ↔ x ∈ q := by
    rcases hcover hx with hn | hc
    · rw [hjN hn]; exact hvproper x hn
    · rw [hjC ⟨hx,hc⟩]; exact hfproper x hx
  have hjne := no_frontier_extension_of_physical_disk_homotopy hDisk hDisk.1 hu huq
    hj.continuousOn hji hjimage hjproper Hcup hcup1 hcupfront hcupi hcupimage hne
  obtain ⟨k,hk,_,hke,hkN,hkC,hkimage,hkcontact,hkcount⟩ :=
    exists_original_boundary_replacement_with_count_decrease he J hJ hN hC hNJ hcover hseam
      hf hfi hg hgi hgfix hgtrace hgavoid pieces hclosed hdis hpieces hconn hremoved
  obtain ⟨G,hG0,hG1,hGR,hGfront,_⟩ := exists_pasted_relative_disk_homotopy
    hN.isCompact.isClosed hC.isCompact.isClosed hcover hseam hj.continuousOn hkN
    (fun x hx => (hkC hx).trans (hjC hx).symm) H
    (fun x => (hH0 x).trans (hjN x.property).symm) hH1
    (fun z hz => (hHfix z hz).trans (hjN z.2.property).symm)
    hjR hHR (fun z => (hHfront z).trans (Iff.of_eq
      (congrArg (fun y : X => y ∈ frontier R) (hjN z.2.property).symm)))
  have hkproper (x : E) (hx : x ∈ J.space) : k x ∈ frontier R ↔ x ∈ q := by
    rw [←hG1 ⟨x,hx⟩]
    exact (hGfront _).trans (hjproper x hx)
  refine ⟨k,hk,hke,?_,hkC,hkproper,hkcontact,hkcount,?_,?_⟩
  · intro x hx
    rw [←hG1 ⟨x,hx⟩]
    exact hGR _
  · exact no_frontier_extension_of_marked_disk_homotopy hDisk hj.continuousOn hk.continuousOn
      (fun x hx => (hjproper x (hDisk.1 hx)).mpr hx) G hG0 hG1 hGfront hjne
  · have hwhole : J.space = N ∪ (J.space ∩ C) := by
      apply Subset.antisymm
      · intro x hx
        exact (hcover hx).elim Or.inl (fun hc => Or.inr ⟨hx,hc⟩)
      · exact union_subset hNJ inter_subset_left
    have hfold : f '' J.space = (f '' (J.space ∩ C)) ∪ (f '' N) := by
      conv_lhs => rw [hwhole,image_union]
      exact union_comm _ _
    have hboth : (f '' (J.space ∩ C)) ∩ (f '' N) ⊆ g '' N := by
      rintro z ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
      have hxy := hfi hx.1 (hNJ hy) (hxz.trans hyz.symm)
      subst y
      exact ⟨x,hy,(hgfix (hseam.subset ⟨hy,hx.2⟩)).trans hxz⟩
    exact exists_open_agreement_of_compact_replacement
      (hN.isCompact.image_of_continuousOn (hf.continuousOn.mono hNJ)).isClosed
      (hN.isCompact.image_of_continuousOn hg.continuousOn).isClosed hfold
      (hkimage.trans (union_comm _ _)) hboth hgavoid

end PoincareConjecture.M76.Dehn.Annuli
