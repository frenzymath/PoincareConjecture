import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.TubeAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_nested_contractible_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ}
    (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : closure (B 0).outer.inside ⊆ interior J.space)
    (hnest : closure (B 1).outer.inside ⊆ (B 0).inner.inside)
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' identityTube L d) = A 0 ∪ A 1) :
    ∃ (H : closure (B 1).inner.inside ≃ₜ closure (B 0).inner.inside)
      (copy : P2 → P2) (a g : P2 → X),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn copy (closure (B 1).inner.inside) ∧
      (∀ x : closure (B 1).inner.inside, copy x = (H x : P2)) ∧
      copy '' closure (B 1).inner.inside = closure (B 0).inner.inside ∧
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      a '' squareAnnulus L d ⊆ τ '' identityTube L d ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ x : closure (B 1).inner.inside, g (copy x) = f x) ∧
      EqOn g f (J.space \ (B 0).outer.inside) ∧ EqOn g f (frontier J.space) ∧
      (∀ p : squareAnnulus L d, g ((B 0).chart p) = a p) ∧
      (∀ z ∈ A 0, ∀ w ∈ J.space, g w = g z → w = z) ∧
      g '' J.space = (f '' closure (B 1).inner.inside ∪
        f '' (J.space \ (B 0).outer.inside)) ∪ a '' squareAnnulus L d := by
  classical
  obtain ⟨eb, H, copy, O, _heb, hH, hcopy, hcopyH, hcopyb, hboundary, hperiod,
    hcopyimage, hO, hOs, hcover, hseamI, hseamP, hdis, hQS, hrim⟩ :=
    exists_nested_contractible_source J hJ (B 0) (B 1) hcontract hnest
  obtain ⟨hcontactO, hcontactI, _⟩ := nested_collar_retained_contacts (B 0) (B 1)
    (hcontract.trans interior_subset) hnest
  obtain ⟨a, haemb, haPL, haTube, _haperiod, haouter, hainner⟩ :=
    exists_resolving_annulus_retained_seams e hcompat hd hwidth hb hbd A
      (fun k ↦ (B k).chart) f τ hτ hfib hvalue 0
  obtain ⟨rI, hrI, hrIH⟩ := hH.symm
  obtain ⟨rC, hrC, hrCc⟩ := (B 0).chart_PL.symm
  have hrImap : MapsTo rI (closure (B 0).inner.inside) (closure (B 1).inner.inside) := by
    intro x hx
    rw [← hrIH ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hrCmap : MapsTo rC (A 0) (squareAnnulus L d) := by
    intro x hx
    rw [← hrCc ⟨x, hx⟩]
    exact ((B 0).chart.symm ⟨x, hx⟩).property
  have hrIcopy (x : closure (B 1).inner.inside) : rI (copy x) = x := by
    rw [hcopyH, ← hrIH, H.symm_apply_apply]
  have hcopyrI (x : closure (B 0).inner.inside) : copy (rI x) = x := by
    rw [← hrIH, hcopyH, H.apply_symm_apply]
  have hrCc' (p : squareAnnulus L d) : rC ((B 0).chart p) = p := by
    rw [← hrCc, (B 0).chart.symm_apply_apply]
  have hcoord (x : A 0) : ((B 0).chart ⟨rC x, hrCmap x.property⟩ : P2) = x := by
    have hp : (⟨rC x, hrCmap x.property⟩ : squareAnnulus L d) = (B 0).chart.symm x :=
      Subtype.ext (hrCc x).symm
    rw [hp, (B 0).chart.apply_symm_apply]
  have hagreeP (x : P2) (hx : x ∈ (B 0).outer.boundary ℝ) : a (rC x) = f x := by
    have hxA := (oriented_collar_boundary_subsets (B 0)).1 hx
    let p : squareAnnulus L d := ⟨rC x, hrCmap hxA⟩
    have hcp : ((B 0).chart p : P2) = x := hcoord ⟨x, hxA⟩
    exact (haouter p (((B 0).outer_depth p).mp (hcp.symm ▸ hx))).trans (congrArg f hcp)
  have hagreeI (x : P2) (hx : x ∈ (B 0).inner.boundary ℝ) :
      a (rC x) = f (rI x) := by
    have hxI := ((B 0).inner.isFinitePLBallPair_closed_inside
      (B 0).inner_simplicial (B 0).inner_injective).1 hx
    have hxA := (oriented_collar_boundary_subsets (B 0)).2 hx
    let p : squareAnnulus L d := ⟨rC x, hrCmap hxA⟩
    have hcp : ((B 0).chart p : P2) = x := hcoord ⟨x, hxA⟩
    have hp : depth L p = d := ((B 0).inner_depth p).mp (hcp.symm ▸ hx)
    have hc1 : ((B 1).chart p : P2) ∈ closure (B 1).inner.inside :=
      ((B 1).inner.isFinitePLBallPair_closed_inside (B 1).inner_simplicial
        (B 1).inner_injective).1 (((B 1).inner_depth p).mpr hp)
    have hval : rI x = (B 1).chart p := by
      rw [← hcp, ← hperiod p hp]
      exact hrIcopy ⟨(B 1).chart p, hc1⟩
    exact (hainner p hp).trans (congrArg f hval.symm)
  obtain ⟨KI, hKI, hKIs, hKIaff⟩ := hrI
  obtain ⟨KC, hKC, hKCs, hKCaff⟩ := hrC
  have hfi : PolyhedralPLInCharts e (f ∘ rI) KI.space :=
    hf.comp_finitePiecewiseAffineOn KI hKI ⟨KI, hKI, rfl, hKIaff⟩
      (fun _ hx ↦ hQS (hrImap (hKIs.subset hx)))
  have hfo : PolyhedralPLInCharts e f O.space :=
    hf.restrict_finite O hO (hOs.subset.trans sdiff_subset)
  have hfa : PolyhedralPLInCharts e (a ∘ rC) KC.space :=
    haPL.comp_finitePiecewiseAffineOn KC hKC ⟨KC, hKC, rfl, hKCaff⟩
      (fun _ hx ↦ hrCmap (hKCs.subset hx))
  obtain ⟨v, hvPL, hvi, hvo⟩ := exists_circle_attachment_map_union hcompat KI O hKI hO hfi hfo
    (fun x hxi hxo ↦ (disjoint_left.mp hdis (hKIs.subset hxi) hxo).elim)
  obtain ⟨KR, hKR, hKRs⟩ := KI.exists_finite_triangulation_union O hKI hO
  have hvR : PolyhedralPLInCharts e v KR.space := by simpa only [hKRs] using hvPL
  obtain ⟨g, hgPL, hgr, hga⟩ := exists_circle_attachment_map_union hcompat KR KC hKR hKC hvR hfa (by
    intro x hxr hxc
    rcases hKRs.subset hxr with hxi | hxo
    · rw [hvi hxi]
      exact (hagreeI x (hseamI.subset ⟨hKIs.subset hxi, hKCs.subset hxc⟩)).symm
    · rw [hvo hxo]
      exact (hagreeP x (hseamP.subset ⟨hKCs.subset hxc, hxo⟩)).symm)
  have hdom : KR.space ∪ KC.space = J.space := by
    rw [hKRs, hKIs, hKCs, union_right_comm]
    exact hcover
  have hgi (x : P2) (hx : x ∈ closure (B 0).inner.inside) : g x = f (rI x) :=
    (hgr (hKRs.symm.subset (Or.inl (hKIs.symm.subset hx)))).trans (hvi (hKIs.symm.subset hx))
  have hgo : EqOn g f O.space := fun x hx ↦
    (hgr (hKRs.symm.subset (Or.inr hx))).trans (hvo hx)
  have hgc (x : P2) (hx : x ∈ A 0) : g x = a (rC x) := hga (hKCs.symm.subset hx)
  have hgcopy (x : closure (B 1).inner.inside) : g (copy x) = f x := by
    rw [hgi (copy x) (hcopyimage.subset (mem_image_of_mem copy x.property)), hrIcopy x]
  have hgca (p : squareAnnulus L d) : g ((B 0).chart p) = a p := by
    rw [hgc _ ((B 0).chart p).property, hrCc' p]
  have hinjA : InjOn g (A 0) := by
    intro x hx y hy heq
    rw [hgc x hx, hgc y hy] at heq
    have hp := haemb.injective (a₁ := ⟨rC x, hrCmap hx⟩) (a₂ := ⟨rC y, hrCmap hy⟩) heq
    exact (hcoord ⟨x, hx⟩).symm.trans
      ((congrArg (fun p ↦ ((B 0).chart p : P2)) hp).trans (hcoord ⟨y, hy⟩))
  have hsingle : ∀ z ∈ A 0, ∀ w ∈ J.space, g w = g z → w = z := by
    intro z hz w hw hwz
    have hzTube : g z ∈ τ '' identityTube L d := by
      rw [hgc z hz]
      exact haTube (mem_image_of_mem a (hrCmap hz))
    have hwTube : g w ∈ τ '' identityTube L d := hwz.symm ▸ hzTube
    rcases hcover.symm.subset hw with (hwI | hwA) | hwO
    · rw [hgi w hwI] at hwTube
      have hwbd : rI w ∈ (B 1).inner.boundary ℝ := hcontactI.subset
        ⟨hpreimage.subset ⟨hQS (hrImap hwI), hwTube⟩, hrImap hwI⟩
      have hwb0 : w ∈ (B 0).inner.boundary ℝ := by
        have h := (hboundary ⟨rI w, hrImap hwI⟩).mpr hwbd
        rwa [hcopyrI ⟨w, hwI⟩] at h
      exact hinjA ((oriented_collar_boundary_subsets (B 0)).2 hwb0) hz hwz
    · exact hinjA hwA hz hwz
    · rw [hgo hwO] at hwTube
      have hwbd := hcontactO.subset ⟨hpreimage.subset ⟨(hOs.subset hwO).1, hwTube⟩,
        hOs.subset hwO⟩
      exact hinjA ((oriented_collar_boundary_subsets (B 0)).1 hwbd) hz hwz
  refine ⟨H, copy, a, g, hH, hcopy, hcopyH, hcopyimage, haemb, haPL, haTube,
    hdom ▸ hgPL, hgcopy, fun x hx ↦ hgo (hOs.symm.subset hx),
    fun x hx ↦ hgo (hrim hx), hgca, hsingle, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hcover.symm.subset hx with (hxI | hxA) | hxO
    · exact Or.inl (Or.inl ⟨rI x, hrImap hxI, (hgi x hxI).symm⟩)
    · exact Or.inr ⟨rC x, hrCmap hxA, (hgc x hxA).symm⟩
    · exact Or.inl (Or.inr ⟨x, hOs.subset hxO, (hgo hxO).symm⟩)
  · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨p, hp, rfl⟩)
    · exact ⟨copy x, hcover.subset (Or.inl (Or.inl
        (hcopyimage.subset (mem_image_of_mem copy hx)))), hgcopy ⟨x, hx⟩⟩
    · exact ⟨x, hx.1, hgo (hOs.symm.subset hx)⟩
    · exact ⟨(B 0).chart ⟨p, hp⟩,
        hcover.subset (Or.inl (Or.inr ((B 0).chart ⟨p, hp⟩).property)), hgca ⟨p, hp⟩⟩

end PoincareConjecture.M76.Dehn.Annuli
