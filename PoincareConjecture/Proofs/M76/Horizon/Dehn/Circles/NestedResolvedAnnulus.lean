import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedAnnulusSource
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulus
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




theorem exists_nested_resolved_annulus_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {m n k : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3)) (Q : Polygon V2 (k + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hinjI : Function.Injective I)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hIsq : I.boundary ℝ ⊆ ball 0 1)
    (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hIP : closure I.inside ⊆ P.inside) (hQI : closure Q.inside ⊆ I.inside)
    (eb : Q.boundary ℝ ≃ₜ I.boundary ℝ) (heb : eb.IsFinitePL)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (c : squareAnnulus L d ≃ₜ ↥(closure P.inside \ I.inside)) (hc : c.IsFinitePL)
    (hnegative : ∀ p : squareAnnulus L d,
      (c p : V2) ∈ P.boundary ℝ ↔ depth L p = -d)
    (hpositive : ∀ p : squareAnnulus L d,
      (c p : V2) ∈ I.boundary ℝ ↔ depth L p = d)
    (f : V2 → X) (hf : PolyhedralPLInCharts e f D)
    (hlocal : IsLocallyInjective (fun x : D => f x))
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (houter : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d),
      (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d) →
        f (c p) = τ ((-d, d), s))
    (hinner : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d)
      (x : Q.boundary ℝ),
      (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), d) →
      (eb x : V2) = c p → f x = τ ((d, d), s))
    (Told : Set V2) (htube : D ∩ f ⁻¹' (τ '' identityTube L d) = Told)
    (htouter : Told ∩ (D \ P.inside) = P.boundary ℝ)
    (htinner : Told ∩ closure Q.inside = Q.boundary ℝ) :
    ∃ (H : closure Q.inside ≃ₜ closure I.inside) (j : V2 → V2)
      (a : P2 → X) (g : V2 → X),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn j (closure Q.inside) ∧
      (∀ x : closure Q.inside, j x = (H x : V2)) ∧
      (∀ x : Q.boundary ℝ, j x = (eb x : V2)) ∧
      j '' closure Q.inside = closure I.inside ∧
      Topology.IsEmbedding (fun p : squareAnnulus L d => a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      PolyhedralPLInCharts e g D ∧ IsLocallyInjective (fun x : D => g x) ∧
      (∀ x : D, ∃ K : Set D, IsCompact K ∧ K ∈ 𝓝 x ∧
        Topology.IsEmbedding (fun y : K => g (y : D))) ∧
      (∀ x ∈ closure Q.inside, g (j x) = f x) ∧
      EqOn g f (D \ P.inside) ∧ EqOn g f R ∧
      (∀ p : squareAnnulus L d, g (c p) = a p) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          τ ((u, max |(u : ℝ)| b), s)) ∧
      g '' D = (f '' closure Q.inside ∪ f '' (D \ P.inside)) ∪ a '' squareAnnulus L d ∧
      (∀ x ∈ closure P.inside \ I.inside,
        ∀ y ∈ closure I.inside ∪ (D \ P.inside), g x = g y ↔ x = y) ∧
      (∀ W : Set X, D ∩ g ⁻¹' W =
        (j '' (closure Q.inside ∩ f ⁻¹' W) ∪ ((D \ P.inside) ∩ f ⁻¹' W)) ∪
          (fun p : squareAnnulus L d => (c p : V2)) '' {p | a p ∈ W}) ∧
      (∀ Z : Set X, (∀ x ∈ D, f x ∈ Z ↔ x ∈ R) →
        Disjoint (τ '' identityTube L d) Z →
        (∀ x ∈ D, g x ∈ Z ↔ x ∈ R) ∧ IsFinitePLBallPair V2 D (D ∩ g ⁻¹' Z)) ∧
      IsFinitePLBallPair V2 D R := by
  classical
  obtain ⟨H, j, hH, hj, hjH, hjb, himage, hcover₀, hcontactI, hcontactP, hdis₀, hball⟩ :=
    exists_nested_annulus_source_disk P I Q hP hinjP hI hinjI hQ hinjQ
      hPsq hIsq hQsq hIP hQI eb heb
  obtain ⟨hcover, hseamI, hseamP, hdis, hclosedC, hclosedO, hrim⟩ :=
    nested_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP
  obtain ⟨_, _, _, hQD⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  have hQsub : closure Q.inside ⊆ D := hQD.trans ball_subset_closedBall
  have hIsub : closure I.inside ⊆ D := fun _ hx => hcover ▸ Or.inl (Or.inl hx)
  have hCsub : closure P.inside \ I.inside ⊆ D := fun _ hx => hcover ▸ Or.inl (Or.inr hx)
  obtain ⟨aa, E, a, _, haemb, haPL, hE, haE, haperiod, haimage, hasub, hacorners, _, _, _⟩ :=
    exists_identity_resolving_annulus e hcompat hd hwidth hb hbd true τ hτ hfib
  have haper (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
        τ ((u, max |(u : ℝ)| b), s) := by
    rw [← hE ((s : AddCircle (4 * L)), u), haE]
    exact haperiod s hs u
  obtain ⟨rI, hrI, hrIH⟩ := hH.symm
  obtain ⟨rC, hrC, hrCc⟩ := hc.symm
  have hrImap : MapsTo rI (closure I.inside) (closure Q.inside) := by
    intro x hx
    rw [← hrIH ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hrCmap : MapsTo rC (closure P.inside \ I.inside) (squareAnnulus L d) := by
    intro x hx
    rw [← hrCc ⟨x, hx⟩]
    exact (c.symm ⟨x, hx⟩).property
  have hrIj (x : closure Q.inside) : rI (j x) = x := by
    rw [hjH, ← hrIH, H.symm_apply_apply]
  have hjrI (x : closure I.inside) : j (rI x) = x := by
    rw [← hrIH, hjH, H.apply_symm_apply]
  have hrCc' (p : squareAnnulus L d) : rC (c p) = p := by
    rw [← hrCc, c.symm_apply_apply]
  have hcoord (x : ↥(closure P.inside \ I.inside)) :
      (c ⟨rC x, hrCmap x.property⟩ : V2) = x := by
    have hp : (⟨rC x, hrCmap x.property⟩ : squareAnnulus L d) = c.symm x :=
      Subtype.ext (hrCc x).symm
    rw [hp, c.apply_symm_apply]
  have hagreeP (x : V2) (hx : x ∈ P.boundary ℝ) :
      a (rC x) = f x := by
    have hxC : x ∈ closure P.inside \ I.inside := (hseamP.symm ▸ hx).1
    let p : squareAnnulus L d := ⟨rC x, hrCmap hxC⟩
    have hcp : (c p : V2) = x := hcoord ⟨x, hxC⟩
    have hpdepth : depth L p = -d := (hnegative p).mp (hcp.symm ▸ hx)
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hpdepth] at hsp
    have hcval := (hacorners s hs).1
    simp only [if_true] at hcval
    exact (congrArg a hsp).trans (hcval.trans ((houter s hs p hsp).symm.trans (congrArg f hcp)))
  have hagreeI (x : V2) (hx : x ∈ I.boundary ℝ) :
      a (rC x) = f (rI x) := by
    have hxI : x ∈ closure I.inside := (hseamI.symm ▸ hx).1
    have hxC : x ∈ closure P.inside \ I.inside := (hseamI.symm ▸ hx).2
    let p : squareAnnulus L d := ⟨rC x, hrCmap hxC⟩
    let q : Q.boundary ℝ := eb.symm ⟨x, hx⟩
    have hq : j q = x := (hjb q).trans (congrArg Subtype.val (eb.apply_symm_apply _))
    have hqQ : (q : V2) ∈ closure Q.inside := by
      obtain ⟨_, hi, hfr, _⟩ := polygon_source_region Q
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
      have hxfront : (q : V2) ∈ frontier (closure Q.inside) := hfr.symm ▸ q.property
      simpa only [isClosed_closure.closure_eq] using frontier_subset_closure hxfront
    have hrq : rI x = q := by rw [← hq]; exact hrIj ⟨q, hqQ⟩
    have hcp : (c p : V2) = x := hcoord ⟨x, hxC⟩
    have hpdepth : depth L p = d := (hpositive p).mp (hcp.symm ▸ hx)
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hpdepth] at hsp
    have hcval := (hacorners s hs).2
    simp only [if_true] at hcval
    have heq : (eb q : V2) = c p :=
      (congrArg Subtype.val (eb.apply_symm_apply _)).trans hcp.symm
    rw [hrq]
    exact (congrArg a hsp).trans (hcval.trans (hinner s hs p q hsp heq).symm)
  have hrIcopy := hrI
  have hrCcopy := hrC
  obtain ⟨KI, hKI, hKIs, _⟩ := hrIcopy
  obtain ⟨KC, hKC, hKCs, _⟩ := hrCcopy
  obtain ⟨_, KO, hKO, hKOs⟩ := exists_polygon_source_complement P hP hinjP hPsq
  have hfi : PolyhedralPLInCharts e (f ∘ rI) KI.space :=
    hf.comp_finitePiecewiseAffineOn KI hKI (by simpa only [hKIs] using hrI)
      (fun _ hx => hQsub (hrImap (hKIs.subset hx)))
  have hfo : PolyhedralPLInCharts e f KO.space :=
    hf.restrict_finite KO hKO (fun _ hx => (hKOs.subset hx).1)
  have hfa : PolyhedralPLInCharts e (a ∘ rC) KC.space :=
    haPL.comp_finitePiecewiseAffineOn KC hKC (by simpa only [hKCs] using hrC)
      (fun _ hx => hrCmap (hKCs.subset hx))
  obtain ⟨v, hvPL, hvi, hvo⟩ := exists_circle_attachment_map_union hcompat KI KO hKI hKO hfi hfo
    (fun x hxi hxo => (Set.disjoint_left.mp hdis (hKIs.subset hxi) (hKOs.subset hxo)).elim)
  obtain ⟨KR, hKR, hKRs⟩ := KI.exists_finite_triangulation_union KO hKI hKO
  have hvR : PolyhedralPLInCharts e v KR.space := by simpa only [hKRs] using hvPL
  obtain ⟨g, hgPL, hgr, hga⟩ := exists_circle_attachment_map_union hcompat KR KC hKR hKC hvR hfa (by
    intro x hxr hxc
    rcases hKRs.subset hxr with hxi | hxo
    · rw [hvi hxi]
      exact (hagreeI x (hseamI ▸ ⟨hKIs.subset hxi, hKCs.subset hxc⟩)).symm
    · rw [hvo hxo]
      exact (hagreeP x (hseamP ▸ ⟨hKCs.subset hxc, hKOs.subset hxo⟩)).symm)
  have hdom : KR.space ∪ KC.space = D := by
    rw [hKRs, hKIs, hKOs, hKCs, union_right_comm]
    exact hcover
  have hgD : PolyhedralPLInCharts e g D := by simpa only [hdom] using hgPL
  have hgi (x : V2) (hx : x ∈ closure I.inside) : g x = f (rI x) :=
    (hgr (hKRs.symm ▸ Or.inl (hKIs.symm ▸ hx))).trans (hvi (hKIs.symm ▸ hx))
  have hgo : EqOn g f (D \ P.inside) := fun x hx =>
    (hgr (hKRs.symm ▸ Or.inr (hKOs.symm ▸ hx))).trans (hvo (hKOs.symm ▸ hx))
  have hgc (x : V2) (hx : x ∈ closure P.inside \ I.inside) : g x = a (rC x) :=
    hga (hKCs.symm ▸ hx)
  have hgj (x : V2) (hx : x ∈ closure Q.inside) : g (j x) = f x := by
    rw [hgi (j x) (himage ▸ mem_image_of_mem j hx), hrIj ⟨x, hx⟩]
  have hgca (p : squareAnnulus L d) : g (c p) = a p := by
    rw [hgc (c p) (c p).property, hrCc' p]
  have hinjC : InjOn g (closure P.inside \ I.inside) := by
    intro x hx y hy heq
    rw [hgc x hx, hgc y hy] at heq
    have hp := haemb.injective (show a (⟨rC x, hrCmap hx⟩ : squareAnnulus L d) =
      a (⟨rC y, hrCmap hy⟩ : squareAnnulus L d) from heq)
    exact (hcoord ⟨x, hx⟩).symm.trans ((congrArg (fun p => (c p : V2)) hp).trans (hcoord ⟨y, hy⟩))
  have hcross : ∀ x ∈ closure P.inside \ I.inside,
      ∀ y ∈ closure I.inside ∪ (D \ P.inside), g x = g y → x = y := by
    intro x hx y hy heq
    have hxtube : g x ∈ τ '' identityTube L d := by
      rw [hgc x hx]
      exact hasub (mem_image_of_mem a (hrCmap hx))
    have hytube : g y ∈ τ '' identityTube L d := heq ▸ hxtube
    rcases hy with hyI | hyO
    · rw [hgi y hyI] at hytube
      have hqbd : rI y ∈ Q.boundary ℝ := htinner ▸
        ⟨htube ▸ ⟨hQsub (hrImap hyI), hytube⟩, hrImap hyI⟩
      have hybd : y ∈ I.boundary ℝ := by
        have he := (hjb ⟨rI y, hqbd⟩).symm.trans (hjrI ⟨y, hyI⟩)
        rw [← show (eb ⟨rI y, hqbd⟩ : V2) = y from he]
        exact (eb ⟨rI y, hqbd⟩).property
      exact hinjC hx (hseamI.symm ▸ hybd).2 heq
    · rw [hgo hyO] at hytube
      have hybd : y ∈ P.boundary ℝ := htouter ▸ ⟨htube ▸ ⟨hyO.1, hytube⟩, hyO⟩
      exact hinjC hx (hseamP.symm ▸ hybd).1 heq
  have hlocalI : IsLocallyInjective (fun x : closure I.inside => g x) := by
    let k : closure I.inside → D := fun x => ⟨rI x, hQsub (hrImap x.property)⟩
    have hk : Continuous k := by
      have he : (fun x : closure I.inside => rI x) = fun x => (H.symm x : V2) :=
        funext fun x => (hrIH x).symm
      apply Continuous.subtype_mk
      rw [he]
      exact continuous_subtype_val.comp H.symm.continuous
    have hki : Function.Injective k := by
      intro x y heq
      apply H.symm.injective
      apply Subtype.ext
      exact (hrIH x).trans ((congrArg (fun z : D => (z : V2)) heq).trans (hrIH y).symm)
    have he : (fun x : closure I.inside => g x) = (fun x : D => f x) ∘ k :=
      funext fun x => hgi x x.property
    rw [he]
    exact hlocal.comp_right hk hki
  have hlocalO : IsLocallyInjective (fun x : ↥(D \ P.inside) => g x) := by
    have he : (fun x : ↥(D \ P.inside) => g x) =
        (fun x : D => f x) ∘ Set.inclusion (show D \ P.inside ⊆ D from sdiff_subset) :=
      funext fun x => hgo x.property
    rw [he]
    exact hlocal.comp_right (continuous_inclusion _) (Set.inclusion_injective _)
  have hlocalR := isLocallyInjective_on_disjoint_closed_union isClosed_closure hclosedO hdis hlocalI hlocalO
  have hlocalC : IsLocallyInjective (fun x : ↥(closure P.inside \ I.inside) => g x) := by
    have hi : Function.Injective (fun x : ↥(closure P.inside \ I.inside) => g x) :=
      fun x y heq => Subtype.ext (hinjC x.property y.property heq)
    exact hi.IsLocallyInjective
  have hlocalAll := isLocallyInjective_on_closed_union hclosedC
    (isClosed_closure.union hclosedO) hlocalC hlocalR hcross
  have hwhole : (closure P.inside \ I.inside) ∪ (closure I.inside ∪ (D \ P.inside)) = D := by
    rw [← union_assoc, union_comm (closure P.inside \ I.inside)]
    exact hcover
  have hlocalg : IsLocallyInjective (fun x : D => g x) := by
    exact hlocalAll.comp_right (Homeomorph.setCongr hwhole.symm).continuous
      (Homeomorph.setCongr hwhole.symm).injective
  have hembed : ∀ x : D, ∃ K : Set D, IsCompact K ∧ K ∈ 𝓝 x ∧
      Topology.IsEmbedding (fun y : K => g (y : D)) := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
    exact exists_compact_embedded_neighborhood hgD.continuousOn.domRestrict hlocalg
  refine ⟨H, j, a, g, hH, hj, hjH, hjb, himage, haemb, haPL, hgD, hlocalg, hembed,
    hgj, hgo, fun _ hx => hgo (hrim hx), hgca, haper, ?_, ?_, ?_, ?_, hball⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcover.symm ▸ hx with (hxI | hxC) | hxO
      · exact Or.inl (Or.inl ⟨rI x, hrImap hxI, (hgi x hxI).symm⟩)
      · exact Or.inr ⟨rC x, hrCmap hxC, (hgc x hxC).symm⟩
      · exact Or.inl (Or.inr ⟨x, hxO, (hgo hxO).symm⟩)
    · rintro _ ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨p, hp, rfl⟩)
      · exact ⟨j x, hIsub (himage ▸ mem_image_of_mem j hx), hgj x hx⟩
      · exact ⟨x, hx.1, hgo hx⟩
      · exact ⟨c ⟨p, hp⟩, hCsub (c ⟨p, hp⟩).property, hgca ⟨p, hp⟩⟩
  · intro x hx y hy
    exact ⟨hcross x hx y hy, fun he => congrArg g he⟩
  · intro W
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      change g x ∈ W at hxW
      rcases hcover.symm ▸ hx with (hxI | hxC) | hxO
      · refine Or.inl (Or.inl ⟨rI x, ⟨hrImap hxI, ?_⟩, hjrI ⟨x, hxI⟩⟩)
        rwa [hgi x hxI] at hxW
      · refine Or.inr ⟨⟨rC x, hrCmap hxC⟩, ?_, hcoord ⟨x, hxC⟩⟩
        rwa [hgc x hxC] at hxW
      · exact Or.inl (Or.inr ⟨hxO, by rwa [hgo hxO] at hxW⟩)
    · rintro ((⟨y, ⟨hy, hyW⟩, rfl⟩ | ⟨hxO, hxW⟩) | ⟨p, hp, rfl⟩)
      · exact ⟨hIsub (himage ▸ mem_image_of_mem j hy), by rwa [mem_preimage, hgj y hy]⟩
      · exact ⟨hxO.1, by rwa [mem_preimage, hgo hxO]⟩
      · exact ⟨hCsub (c p).property, by rwa [mem_preimage, hgca p]⟩
  · intro Z hproper havoid
    obtain ⟨_, _, _, hPD⟩ := polygon_source_region P
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
    have hnewproper : ∀ x ∈ D, g x ∈ Z ↔ x ∈ R := by
      intro x hx
      rcases hcover.symm ▸ hx with (hxI | hxC) | hxO
      · have hleft : g x ∉ Z := by
          rw [hgi x hxI]
          intro hZ
          exact (ne_of_lt (hQD (hrImap hxI))) ((hproper (rI x) (hQsub (hrImap hxI))).mp hZ)
        have hright : x ∉ R := fun hr => (ne_of_lt (hPD (subset_closure (hIP hxI)))) hr
        exact iff_of_false hleft hright
      · have hleft : g x ∉ Z := by
          rw [hgc x hxC]
          exact Set.disjoint_left.mp havoid (hasub (mem_image_of_mem a (hrCmap hxC)))
        have hright : x ∉ R := fun hr => (ne_of_lt (hPD hxC.1)) hr
        exact iff_of_false hleft hright
      · rw [hgo hxO]
        exact hproper x hxO.1
    refine ⟨hnewproper, ?_⟩
    have hr : D ∩ g ⁻¹' Z = R := by
      ext x
      exact ⟨fun hx => (hnewproper x hx.1).mp hx.2,
        fun hx => ⟨sphere_subset_closedBall hx, (hnewproper x (sphere_subset_closedBall hx)).mpr hx⟩⟩
    rw [hr]
    exact hball

end Dehn
