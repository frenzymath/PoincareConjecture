import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.DisjointAnnulusSource
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulusPair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusBoundaryParameters
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ClosedSeamLocalInjectivity

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip
open scoped Topology
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1

theorem exists_disjoint_resolved_annuli_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {m n : Bool → ℕ}
    (P : (i : Bool) → Polygon V2 (m i + 3)) (I : (i : Bool) → Polygon V2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinjP : ∀ i, Function.Injective (P i))
    (hI : ∀ i, (I i).HasSimplicialEdges) (hinjI : ∀ i, Function.Injective (I i))
    (hPsq : ∀ i, (P i).boundary ℝ ⊆ ball 0 1)
    (hIsq : ∀ i, (I i).boundary ℝ ⊆ ball 0 1)
    (hIP : ∀ i, closure (I i).inside ⊆ (P i).inside)
    (hdisP : Disjoint (closure (P false).inside) (closure (P true).inside))
    (eb : (I false).boundary ℝ ≃ₜ (I true).boundary ℝ) (heb : eb.IsFinitePL)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (c : (i : Bool) → squareAnnulus L d ≃ₜ ↥(closure (P i).inside \ (I i).inside))
    (hc : ∀ i, (c i).IsFinitePL)
    (hnegative : ∀ i (p : squareAnnulus L d),
      (c i p : V2) ∈ (P i).boundary ℝ ↔ depth L p = -d)
    (hpositive : ∀ i (p : squareAnnulus L d),
      (c i p : V2) ∈ (I i).boundary ℝ ↔ depth L p = d)
    (f : V2 → X) (hf : PolyhedralPLInCharts e f D)
    (hlocal : IsLocallyInjective (fun x : D => f x))
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (houter : ∀ i (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d),
      (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d) →
        f (c i p) = τ ((-d, if i then d else -d), s))
    (hinner : ∀ i (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d)
      (x : (I (!i)).boundary ℝ),
      (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), d) →
      (exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ)) eb i x : V2) = c i p →
        f x = τ ((d, if i then d else -d), s))
    (Told : Set V2) (htube : D ∩ f ⁻¹' (τ '' identityTube L d) = Told)
    (htouter : Told ∩ (D \ ((P false).inside ∪ (P true).inside)) =
      (P false).boundary ℝ ∪ (P true).boundary ℝ)
    (htinner : ∀ i, Told ∩ closure (I i).inside = (I i).boundary ℝ) :
    let S := fun i => closure (I i).inside
    let C := fun i => closure (P i).inside \ (I i).inside
    let O := D \ ((P false).inside ∪ (P true).inside)
    ∃ (H : S false ≃ₜ S true) (j : Bool → V2 → V2) (a : Bool → P2 → X) (g : V2 → X),
      H.IsFinitePL ∧
      (∀ i, FinitePiecewiseAffineOn (j i) (S (!i))) ∧
      (∀ i (x : S (!i)),
        j i x = (exchangedCircleHomeomorph (A := fun k => ↥(S k)) H i x : V2)) ∧
      (∀ i, j i '' S (!i) = S i) ∧
      (∀ i, ∀ x ∈ S (!i), j (!i) (j i x) = x) ∧
      (∀ i (x : (I (!i)).boundary ℝ), j i x =
        (exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ)) eb i x : V2)) ∧
      (∀ i, Topology.IsEmbedding (fun p : squareAnnulus L d => a i p) ∧
        PolyhedralPLInCharts e (a i) (squareAnnulus L d)) ∧
      Disjoint (a false '' squareAnnulus L d) (a true '' squareAnnulus L d) ∧
      PolyhedralPLInCharts e g D ∧ IsLocallyInjective (fun x : D => g x) ∧
      (∀ x : D, ∃ K : Set D, IsCompact K ∧ K ∈ 𝓝 x ∧
        Topology.IsEmbedding (fun y : K => g (y : D))) ∧
      (∀ i, ∀ x ∈ S (!i), g (j i x) = f x) ∧ EqOn g f O ∧ EqOn g f R ∧
      (∀ i (p : squareAnnulus L d), g (c i p) = a i p) ∧
      (∀ i (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a i (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          τ ((u, signedHeight b i u), s)) ∧
      g '' D = ((f '' S false ∪ f '' S true) ∪ f '' O) ∪
        (a false '' squareAnnulus L d ∪ a true '' squareAnnulus L d) ∧
      (∀ x ∈ C false ∪ C true, ∀ y ∈ (S false ∪ S true) ∪ O,
        g x = g y ↔ x = y) ∧
      (∀ W : Set X, D ∩ g ⁻¹' W =
        ((j false '' (S true ∩ f ⁻¹' W) ∪ j true '' (S false ∩ f ⁻¹' W)) ∪ (O ∩ f ⁻¹' W)) ∪
          ((fun p : squareAnnulus L d => (c false p : V2)) '' {p | a false p ∈ W} ∪
           (fun p : squareAnnulus L d => (c true p : V2)) '' {p | a true p ∈ W})) ∧
      (∀ Z : Set X, (∀ x ∈ D, f x ∈ Z ↔ x ∈ R) →
        Disjoint (τ '' identityTube L d) Z →
        (∀ x ∈ D, g x ∈ Z ↔ x ∈ R) ∧ IsFinitePLBallPair V2 D (D ∩ g ⁻¹' Z)) := by
  classical
  let S := fun i => closure (I i).inside
  let C := fun i => closure (P i).inside \ (I i).inside
  let O := D \ ((P false).inside ∪ (P true).inside)
  obtain ⟨hcover, hseamI, hseamP, hdisI, hdisIO, hdisC, hdisIC, hclosedC, hclosedO,
      hSball, hCball, hrim⟩ :=
    disjoint_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP hdisP
  have hSsub (i : Bool) : S i ⊆ D := (hSball i).trans ball_subset_closedBall
  have hCsub (i : Bool) : C i ⊆ D := (hCball i).trans ball_subset_closedBall
  obtain ⟨H, j0, j1, hH, hj0, hj1, hj0H, hj1H, hemb0, hemb1, him0, him1,
    hinv0, hinv1, hb0, hb1, _⟩ := exists_disjoint_circle_source_disk
      (I false) (I true) (hI false) (hinjI false) (hI true) (hinjI true)
      (hIsq false) (hIsq true) hdisI eb heb
  let j : Bool → V2 → V2 := fun i => if i then j0 else j1
  have hj (i : Bool) : FinitePiecewiseAffineOn (j i) (S (!i)) := by cases i <;> assumption
  have hjH (i : Bool) (x : S (!i)) :
      j i x = (exchangedCircleHomeomorph (A := fun k => ↥(S k)) H i x : V2) := by
    cases i
    · exact hj1H x
    · exact hj0H x
  have hjimage (i : Bool) : j i '' S (!i) = S i := by cases i <;> assumption
  have hjmap (i : Bool) : MapsTo (j i) (S (!i)) (S i) :=
    fun _ hx => hjimage i ▸ mem_image_of_mem (j i) hx
  have hjinv (i : Bool) (x : V2) (hx : x ∈ S (!i)) : j (!i) (j i x) = x := by
    cases i
    · exact hinv1 x hx
    · exact hinv0 x hx
  have hjb (i : Bool) (x : (I (!i)).boundary ℝ) :
      j i x =
        (exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ)) eb i x : V2) := by
    cases i
    · exact hb1 x
    · exact hb0 x
  have hji (i : Bool) : InjOn (j i) (S (!i)) := by
    intro x hx y hy heq
    exact (hjinv i x hx).symm.trans ((congrArg (j (!i)) heq).trans (hjinv i y hy))
  obtain ⟨a, ha, hadis⟩ :=
    exists_identity_resolving_annulus_pair e hcompat hd hwidth hb hbd τ hτ hfib
  have hasub (i : Bool) : a i '' squareAnnulus L d ⊆ τ '' identityTube L d := by
    rw [(ha i).2.2.2.1]
    exact image_mono (image_subset_iff.mpr (identity_strip_mapsTo hbd.le i))
  choose rC hrC hrCc using fun i => (hc i).symm
  have hrmap (i : Bool) : MapsTo (rC i) (C i) (squareAnnulus L d) := by
    intro x hx
    rw [← hrCc i ⟨x, hx⟩]
    exact ((c i).symm ⟨x, hx⟩).property
  have hrci (i : Bool) (p : squareAnnulus L d) : rC i (c i p) = p := by
    rw [← hrCc, (c i).symm_apply_apply]
  have hcoord (i : Bool) (x : C i) : (c i ⟨rC i x, hrmap i x.property⟩ : V2) = x := by
    have he : (⟨rC i x, hrmap i x.property⟩ : squareAnnulus L d) = (c i).symm x :=
      Subtype.ext (hrCc i x).symm
    rw [he, (c i).apply_symm_apply]
  have hcorners (i : Bool) (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) :
      a i (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) =
        τ ((-d, if i then d else -d), s) ∧
      a i (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) =
        τ ((d, if i then d else -d), s) := by
    have hm := (ha i).2.2.1 s hs ⟨-d, ⟨le_rfl, by linarith⟩⟩
    have hp := (ha i).2.2.1 s hs ⟨d, ⟨by linarith, le_rfl⟩⟩
    simpa only [signedHeight, height, abs_neg, abs_of_pos hd, max_eq_left hbd.le] using
      And.intro hm hp
  have hagreeP (i : Bool) (x : V2) (hx : x ∈ (P i).boundary ℝ) :
      a i (rC i x) = f x := by
    have hxC : x ∈ C i := ((hseamP i).symm ▸ hx).1
    let p : squareAnnulus L d := ⟨rC i x, hrmap i hxC⟩
    have hcp : (c i p : V2) = x := hcoord i ⟨x, hxC⟩
    have hdepth := (hnegative i p).mp (hcp.symm ▸ hx)
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hdepth] at hsp
    exact (congrArg (a i) hsp).trans ((hcorners i s hs).1.trans
      ((houter i s hs p hsp).symm.trans (congrArg f hcp)))
  have hboundaryS (i : Bool) : (I i).boundary ℝ ⊆ S i := by
    obtain ⟨hball, _⟩ := polygon_source_region (I i)
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (hI i) (hinjI i) (convex_ball _ _) (hIsq i)
    exact hball.1
  have hagreeI (i : Bool) (x : V2) (hx : x ∈ (I i).boundary ℝ) :
      a i (rC i x) = f (j (!i) x) := by
    have hxC : x ∈ C i := ((hseamI i).symm ▸ hx).2
    let p : squareAnnulus L d := ⟨rC i x, hrmap i hxC⟩
    let E := exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ)) eb i
    let q : (I (!i)).boundary ℝ := E.symm ⟨x, hx⟩
    have hq : j i q = x := (hjb i q).trans
      (congrArg Subtype.val (E.apply_symm_apply _))
    have hrq : j (!i) x = q := by rw [← hq]; exact hjinv i q (hboundaryS (!i) q.property)
    have hcp : (c i p : V2) = x := hcoord i ⟨x, hxC⟩
    have hdepth := (hpositive i p).mp (hcp.symm ▸ hx)
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hdepth] at hsp
    have heq : (E q : V2) = c i p :=
      (congrArg Subtype.val (E.apply_symm_apply _)).trans hcp.symm
    rw [hrq]
    exact (congrArg (a i) hsp).trans ((hcorners i s hs).2.trans (hinner i s hs p q hsp heq).symm)
  have hjtarget (i : Bool) : FinitePiecewiseAffineOn (j (!i)) (S i) := by
    simpa only [Bool.not_not] using hj (!i)
  have hjtargetmap (i : Bool) : MapsTo (j (!i)) (S i) (S (!i)) := by
    simpa only [Bool.not_not] using hjmap (!i)
  choose KI hKI hKIs hKIaff using fun i => hjtarget i
  choose KC hKC hKCs hKCaff using fun i => hrC i
  obtain ⟨KO, hKO, hKOs⟩ := exists_two_polygon_source_complement
    (P false) (P true) (hP false) (hinjP false) (hP true) (hinjP true) (hPsq false) (hPsq true)
  have hfi (i : Bool) : PolyhedralPLInCharts e (f ∘ j (!i)) (KI i).space :=
    hf.comp_finitePiecewiseAffineOn (KI i) (hKI i) (by simpa only [hKIs i] using hjtarget i)
      (fun _ hx => hSsub (!i) (hjtargetmap i ((hKIs i).subset hx)))
  have hfa (i : Bool) : PolyhedralPLInCharts e (a i ∘ rC i) (KC i).space :=
    (ha i).2.1.comp_finitePiecewiseAffineOn (KC i) (hKC i) (by simpa only [hKCs i] using hrC i)
      (fun _ hx => hrmap i ((hKCs i).subset hx))
  have hfo : PolyhedralPLInCharts e f KO.space :=
    hf.restrict_finite KO hKO (fun _ hx => (hKOs.subset hx).1)
  obtain ⟨vI, hvI, hvi0, hvi1⟩ := exists_circle_attachment_map_union hcompat
    (KI false) (KI true) (hKI false) (hKI true) (hfi false) (hfi true)
      (fun x hx hy =>
        (Set.disjoint_left.mp hdisI ((hKIs false).subset hx) ((hKIs true).subset hy)).elim)
  obtain ⟨KII, hKII, hKIIs⟩ :=
    (KI false).exists_finite_triangulation_union (KI true) (hKI false) (hKI true)
  obtain ⟨vR, hvR, hvri, hvro⟩ := exists_circle_attachment_map_union hcompat KII KO hKII hKO
    (by simpa only [hKIIs] using hvI) hfo (by
      intro x hx hy
      have hxI : x ∈ S false ∪ S true := by simpa only [hKIIs, hKIs] using hx
      exact (Set.disjoint_left.mp hdisIO hxI (hKOs.subset hy)).elim)
  obtain ⟨KR, hKR, hKRs⟩ := KII.exists_finite_triangulation_union KO hKII hKO
  obtain ⟨vA, hvA, hva0, hva1⟩ := exists_circle_attachment_map_union hcompat
    (KC false) (KC true) (hKC false) (hKC true) (hfa false) (hfa true)
      (fun x hx hy =>
        (Set.disjoint_left.mp hdisC ((hKCs false).subset hx) ((hKCs true).subset hy)).elim)
  obtain ⟨KA, hKA, hKAs⟩ :=
    (KC false).exists_finite_triangulation_union (KC true) (hKC false) (hKC true)
  have hretI (i : Bool) (x : V2) (hx : x ∈ S i) : vR x = f (j (!i) x) := by
    cases i
    · exact (hvri (hKIIs.symm ▸ Or.inl ((hKIs false).symm ▸ hx))).trans
        (hvi0 ((hKIs false).symm ▸ hx))
    · exact (hvri (hKIIs.symm ▸ Or.inr ((hKIs true).symm ▸ hx))).trans
        (hvi1 ((hKIs true).symm ▸ hx))
  have hretO (x : V2) (hx : x ∈ O) : vR x = f x := hvro (hKOs.symm ▸ hx)
  have hann (i : Bool) (x : V2) (hx : x ∈ C i) : vA x = a i (rC i x) := by
    cases i
    · exact hva0 ((hKCs false).symm ▸ hx)
    · exact hva1 ((hKCs true).symm ▸ hx)
  have hKRspace : KR.space = (S false ∪ S true) ∪ O := by rw [hKRs, hKIIs, hKIs, hKIs, hKOs]
  have hKAspace : KA.space = C false ∪ C true := by rw [hKAs, hKCs, hKCs]
  have hagree (i : Bool) (x : V2) (hx : x ∈ C i) (hy : x ∈ (S false ∪ S true) ∪ O) :
      vR x = vA x := by
    rw [hann i x hx]
    rcases hy with (hy0 | hy1) | hyO
    · cases i
      · exact (hretI false x hy0).trans (hagreeI false x (hseamI false ▸ ⟨hy0, hx⟩)).symm
      · exact (Set.disjoint_left.mp (hdisIC true) hy0 hx).elim
    · cases i
      · exact (Set.disjoint_left.mp (hdisIC false) hy1 hx).elim
      · exact (hretI true x hy1).trans (hagreeI true x (hseamI true ▸ ⟨hy1, hx⟩)).symm
    · exact (hretO x hyO).trans (hagreeP i x (hseamP i ▸ ⟨hx, hyO⟩)).symm
  obtain ⟨g, hg, hgr, hga⟩ := exists_circle_attachment_map_union hcompat KR KA hKR hKA
    (by simpa only [hKRs] using hvR) (by simpa only [hKAs] using hvA) (by
      intro x hx hy
      rcases hKAspace.subset hy with hy0 | hy1
      · exact hagree false x hy0 (hKRspace.subset hx)
      · exact hagree true x hy1 (hKRspace.subset hx))
  have hdom : KR.space ∪ KA.space = D := by rw [hKRspace, hKAspace]; exact hcover
  have hgD : PolyhedralPLInCharts e g D := by simpa only [hdom] using hg
  have hgi (i : Bool) (x : V2) (hx : x ∈ S i) : g x = f (j (!i) x) := by
    have hxR : x ∈ (S false ∪ S true) ∪ O := by
      cases i
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
    exact (hgr (hKRspace.symm ▸ hxR)).trans (hretI i x hx)
  have hgo : EqOn g f O := fun x hx =>
    (hgr (hKRspace.symm ▸ Or.inr hx)).trans (hretO x hx)
  have hgc (i : Bool) (x : V2) (hx : x ∈ C i) : g x = a i (rC i x) := by
    have hxA : x ∈ C false ∪ C true := by
      cases i
      · exact Or.inl hx
      · exact Or.inr hx
    exact (hga (hKAspace.symm ▸ hxA)).trans (hann i x hx)
  have hgj (i : Bool) (x : V2) (hx : x ∈ S (!i)) : g (j i x) = f x := by
    rw [hgi i (j i x) (hjmap i hx), hjinv i x hx]
  have hgca (i : Bool) (p : squareAnnulus L d) : g (c i p) = a i p := by
    rw [hgc i (c i p) (c i p).property, hrci i p]
  have hinjCi (i : Bool) : InjOn g (C i) := by
    intro x hx y hy heq
    rw [hgc i x hx, hgc i y hy] at heq
    have hp := (ha i).1.injective (show a i (⟨rC i x, hrmap i hx⟩ : squareAnnulus L d) =
      a i (⟨rC i y, hrmap i hy⟩ : squareAnnulus L d) from heq)
    exact (hcoord i ⟨x, hx⟩).symm.trans
      ((congrArg (fun p => (c i p : V2)) hp).trans (hcoord i ⟨y, hy⟩))
  have hCimages (i : Bool) (x : V2) (hx : x ∈ C i) : g x ∈ a i '' squareAnnulus L d :=
    ⟨rC i x, hrmap i hx, (hgc i x hx).symm⟩
  have hinjC : InjOn g (C false ∪ C true) := by
    intro x hx y hy heq
    rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
    · exact hinjCi false hx0 hy0 heq
    · exact (Set.disjoint_left.mp hadis (hCimages true y hy1) (heq ▸ hCimages false x hx0)).elim
    · exact (Set.disjoint_left.mp hadis (hCimages true x hx1)
        (heq.symm ▸ hCimages false y hy0)).elim
    · exact hinjCi true hx1 hy1 heq
  have hcross : ∀ x ∈ C false ∪ C true, ∀ y ∈ (S false ∪ S true) ∪ O,
      g x = g y → x = y := by
    intro x hx y hy heq
    have hxtube : g x ∈ τ '' identityTube L d := by
      rcases hx with hx0 | hx1
      · exact hasub false (hCimages false x hx0)
      · exact hasub true (hCimages true x hx1)
    have hytube : g y ∈ τ '' identityTube L d := heq ▸ hxtube
    have hcap (i : Bool) (hyI : y ∈ S i) : y ∈ C i := by
      rw [hgi i y hyI] at hytube
      have hqbd : j (!i) y ∈ (I (!i)).boundary ℝ := htinner (!i) ▸
        ⟨htube ▸ ⟨hSsub (!i) (hjtargetmap i hyI), hytube⟩, hjtargetmap i hyI⟩
      have hybd : y ∈ (I i).boundary ℝ := by
        have he := (hjb i ⟨j (!i) y, hqbd⟩).symm.trans
          (by simpa only [Bool.not_not] using
            hjinv (!i) y (by simpa only [Bool.not_not] using hyI))
        let E := exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ)) eb i
        rw [← show (E ⟨j (!i) y, hqbd⟩ : V2) = y from he]
        exact (E ⟨j (!i) y, hqbd⟩).property
      exact ((hseamI i).symm ▸ hybd).2
    apply hinjC hx ?_ heq
    rcases hy with (hy0 | hy1) | hyO
    · exact Or.inl (hcap false hy0)
    · exact Or.inr (hcap true hy1)
    · rw [hgo hyO] at hytube
      have hybd := htouter ▸ (show y ∈ Told ∩ O from ⟨htube ▸ ⟨hyO.1, hytube⟩, hyO⟩)
      exact hybd.elim (fun h => Or.inl (((hseamP false).symm ▸ h).1))
        (fun h => Or.inr (((hseamP true).symm ▸ h).1))
  have hlocalI (i : Bool) : IsLocallyInjective (fun x : S i => g x) := by
    let k : S i → D := fun x => ⟨j (!i) x, hSsub (!i) (hjtargetmap i x.property)⟩
    have hk : Continuous k := ((hjtarget i).continuousOn.domRestrict).subtype_mk _
    have hki : Function.Injective k := by
      intro x y heq
      apply Subtype.ext
      exact hji (!i) (by simpa only [Bool.not_not] using x.property)
        (by simpa only [Bool.not_not] using y.property) (congrArg (fun z : D => (z : V2)) heq)
    have he : (fun x : S i => g x) = (fun x : D => f x) ∘ k := funext fun x => hgi i x x.property
    rw [he]
    exact hlocal.comp_right hk hki
  have hlocalO : IsLocallyInjective (fun x : O => g x) := by
    have he : (fun x : O => g x) =
        (fun x : D => f x) ∘ Set.inclusion (show O ⊆ D from sdiff_subset) :=
      funext fun x => hgo x.property
    rw [he]
    exact hlocal.comp_right (continuous_inclusion _) (Set.inclusion_injective _)
  have hlocalII := isLocallyInjective_on_disjoint_closed_union isClosed_closure isClosed_closure
    hdisI (hlocalI false) (hlocalI true)
  have hlocalR := isLocallyInjective_on_disjoint_closed_union
    (isClosed_closure.union isClosed_closure) hclosedO hdisIO hlocalII hlocalO
  have hlocalC : IsLocallyInjective (fun x : ↥(C false ∪ C true) => g x) := by
    have hi : Function.Injective (fun x : ↥(C false ∪ C true) => g x) :=
      fun x y heq => Subtype.ext (hinjC x.property y.property heq)
    exact hi.IsLocallyInjective
  have hlocalAll := isLocallyInjective_on_closed_union ((hclosedC false).union (hclosedC true))
    ((isClosed_closure.union isClosed_closure).union hclosedO) hlocalC hlocalR hcross
  have hwhole : (C false ∪ C true) ∪ ((S false ∪ S true) ∪ O) = D := by
    rw [union_comm]; exact hcover
  have hlocalg : IsLocallyInjective (fun x : D => g x) :=
    hlocalAll.comp_right (Homeomorph.setCongr hwhole.symm).continuous
      (Homeomorph.setCongr hwhole.symm).injective
  have hembed : ∀ x : D, ∃ K : Set D, IsCompact K ∧ K ∈ 𝓝 x ∧
      Topology.IsEmbedding (fun y : K => g (y : D)) := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
    exact exists_compact_embedded_neighborhood hgD.continuousOn.domRestrict hlocalg
  refine ⟨H, j, a, g, hH, hj, hjH, hjimage, hjinv, hjb, fun i => ⟨(ha i).1, (ha i).2.1⟩,
    hadis.symm, hgD, hlocalg, hembed, hgj, hgo, fun _ hx => hgo (hrim hx), hgca,
    fun i => (ha i).2.2.1, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcover.symm ▸ hx with ((hx0 | hx1) | hxO) | (hxC0 | hxC1)
      · exact Or.inl (Or.inl (Or.inr ⟨j true x, hjtargetmap false hx0, (hgi false x hx0).symm⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨j false x, hjtargetmap true hx1, (hgi true x hx1).symm⟩))
      · exact Or.inl (Or.inr ⟨x, hxO, (hgo hxO).symm⟩)
      · exact Or.inr (Or.inl (hCimages false x hxC0))
      · exact Or.inr (Or.inr (hCimages true x hxC1))
    · rintro _ (((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩))
      · exact ⟨j true x, hSsub true (hjmap true hx), hgj true x hx⟩
      · exact ⟨j false x, hSsub false (hjmap false hx), hgj false x hx⟩
      · exact ⟨x, hx.1, hgo hx⟩
      · exact ⟨c false ⟨p, hp⟩, hCsub false (c false ⟨p, hp⟩).property, hgca false ⟨p, hp⟩⟩
      · exact ⟨c true ⟨p, hp⟩, hCsub true (c true ⟨p, hp⟩).property, hgca true ⟨p, hp⟩⟩
  · intro x hx y hy
    exact ⟨hcross x hx y hy, congrArg g⟩
  · intro W
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      change g x ∈ W at hxW
      rcases hcover.symm ▸ hx with ((hx0 | hx1) | hxO) | (hxC0 | hxC1)
      · exact Or.inl (Or.inl (Or.inl ⟨j true x,
          ⟨hjtargetmap false hx0, by rwa [hgi false x hx0] at hxW⟩, hjinv true x hx0⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨j false x,
          ⟨hjtargetmap true hx1, by rwa [hgi true x hx1] at hxW⟩, hjinv false x hx1⟩))
      · exact Or.inl (Or.inr ⟨hxO, by rwa [hgo hxO] at hxW⟩)
      · exact Or.inr (Or.inl ⟨⟨rC false x, hrmap false hxC0⟩,
          by rwa [hgc false x hxC0] at hxW, hcoord false ⟨x, hxC0⟩⟩)
      · exact Or.inr (Or.inr ⟨⟨rC true x, hrmap true hxC1⟩,
          by rwa [hgc true x hxC1] at hxW, hcoord true ⟨x, hxC1⟩⟩)
    · rintro (((⟨y, ⟨hy, hyW⟩, rfl⟩ | ⟨y, ⟨hy, hyW⟩, rfl⟩) | ⟨hxO, hxW⟩) |
        (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩))
      · exact ⟨hSsub false (hjmap false hy), by rwa [mem_preimage, hgj false y hy]⟩
      · exact ⟨hSsub true (hjmap true hy), by rwa [mem_preimage, hgj true y hy]⟩
      · exact ⟨hxO.1, by rwa [mem_preimage, hgo hxO]⟩
      · exact ⟨hCsub false (c false p).property, by rwa [mem_preimage, hgca false p]⟩
      · exact ⟨hCsub true (c true p).property, by rwa [mem_preimage, hgca true p]⟩
  · intro Z hproper havoid
    have hnewproper : ∀ x ∈ D, g x ∈ Z ↔ x ∈ R := by
      intro x hx
      have hcap (i : Bool) (hi : x ∈ S i) : g x ∈ Z ↔ x ∈ R := by
        have hleft : g x ∉ Z := by
          rw [hgi i x hi]
          intro hZ
          exact (ne_of_lt (hSball (!i) (hjtargetmap i hi)))
            ((hproper _ (hSsub (!i) (hjtargetmap i hi))).mp hZ)
        exact iff_of_false hleft (fun hr => (ne_of_lt (hSball i hi)) hr)
      have hannulus (i : Bool) (hi : x ∈ C i) : g x ∈ Z ↔ x ∈ R :=
        iff_of_false (Set.disjoint_left.mp havoid (hasub i (hCimages i x hi)))
          (fun hr => (ne_of_lt (hCball i hi)) hr)
      rcases hcover.symm ▸ hx with ((hx0 | hx1) | hxO) | (hxC0 | hxC1)
      · exact hcap false hx0
      · exact hcap true hx1
      · rw [hgo hxO]; exact hproper x hxO.1
      · exact hannulus false hxC0
      · exact hannulus true hxC1
    refine ⟨hnewproper, ?_⟩
    have hr : D ∩ g ⁻¹' Z = R := by
      ext x
      exact ⟨fun hx => (hnewproper x hx.1).mp hx.2,
        fun hx =>
          ⟨sphere_subset_closedBall hx, (hnewproper x (sphere_subset_closedBall hx)).mpr hx⟩⟩
    rw [hr]
    exact isFinitePLBallPair_unit_cube

end Dehn
