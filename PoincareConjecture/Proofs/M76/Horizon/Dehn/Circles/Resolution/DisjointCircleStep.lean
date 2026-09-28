import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.CollarGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OriginalRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.BoundaryCorrespondence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.DisjointSourceRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OrdinaryModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.LocalInjectivity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace PoincareConjecture.M76.Dehn.PairedCircleCollars

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

private theorem regionChart_value {A : Set V2}
    (B : _root_.Dehn.OrientedPolygonCollar L d A) (p : squareAnnulus L d) :
    (B.regionChart p : V2) = B.chart p := rfl

theorem exists_disjoint_boundary_data (G : PairedCircleCollars D L d)
    (hd : 0 < d) (hwidth : 4 * d < L) :
    let B := fun b : Bool => G.collar (if b then 1 else 0)
    let I := fun b => (B b).inner
    let c := fun b => (B b).regionChart
    ∃ eb : (I false).boundary ℝ ≃ₜ (I true).boundary ℝ,
      eb.IsFinitePL ∧
      (∀ b s (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d),
        (p : P2) = annulusMap L G.length_pos ((s : AddCircle (4 * L)), -d) →
          f (c b p) = G.tube ((-d, if b then d else -d), s)) ∧
      (∀ b s (_hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d)
        (x : (I (!b)).boundary ℝ),
        (p : P2) = annulusMap L G.length_pos ((s : AddCircle (4 * L)), d) →
        (_root_.Dehn.exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ))
          eb b x : V2) = c b p →
          f x = G.tube ((d, if b then d else -d), s)) := by
  classical
  dsimp only
  let B := fun b : Bool => G.collar (if b then 1 else 0)
  let I := fun b => (B b).inner
  let c := fun b => (B b).regionChart
  obtain ⟨eb, heb, _, _, heval⟩ :=
    _root_.Dehn.exists_synchronized_collar_boundary_homeomorph
      (G.collar 0).inner (G.collar 1).inner
      (G.collar 0).inner_simplicial (G.collar 0).inner_injective
      (G.collar 0).boundary_subset_source.2 (G.collar 1).boundary_subset_source.2
      (G.collar 0).chart (G.collar 1).chart
      (G.collar 0).chart_PL (G.collar 1).chart_PL
      (G.collar 0).inner_depth (G.collar 1).inner_depth
  have hswap (b : Bool) (p : squareAnnulus L d) (hp : depth L p = d) :
      (_root_.Dehn.exchangedCircleHomeomorph (A := fun k => ↥((I k).boundary ℝ))
        eb b ⟨c (!b) p, ((B (!b)).inner_depth p).mpr hp⟩ : V2) = c b p := by
    cases b
    · have he : eb ⟨(G.collar 0).chart p, ((G.collar 0).inner_depth p).mpr hp⟩ =
          ⟨(G.collar 1).chart p, ((G.collar 1).inner_depth p).mpr hp⟩ :=
        Subtype.ext (heval p hp)
      have hh := congrArg eb.symm he
      simpa [Homeomorph.symm_apply_apply, c, B, I, _root_.Dehn.exchangedCircleHomeomorph,
        regionChart_value] using (congrArg Subtype.val hh).symm
    · exact heval p hp
  refine ⟨eb, heb, ?_, ?_⟩
  · intro b s hs p hp
    have h := G.period_value (if b then 1 else 0) s hs
      ⟨-d, ⟨le_rfl, by linarith⟩⟩ p hp
    cases b <;> simpa [sourceTubeDiagonal, regionChart_value] using h
  · intro b s hs p x hp hx
    have hdepth : depth L p = d := by
      rw [hp]
      exact depth_annulusMap G.length_pos (by simpa only [abs_of_pos hd] using hwidth) _
    let y : (I (!b)).boundary ℝ := ⟨c (!b) p, ((B (!b)).inner_depth p).mpr hdepth⟩
    have hxy : x = y :=
      (_root_.Dehn.exchangedCircleHomeomorph
        (A := fun k => ↥((I k).boundary ℝ)) eb b).injective
          (Subtype.ext (hx.trans (hswap b p hdepth).symm))
    rw [hxy]
    have h := G.period_value (if !b then 1 else 0) s hs
      ⟨d, ⟨by linarith, le_rfl⟩⟩ p hp
    cases b <;> simpa [sourceTubeDiagonal, y, c, B, I, regionChart_value] using h



theorem exists_disjoint_step [T2Space X] (G : PairedCircleCollars D L d)
    (hd : 0 < d) (hwidth : 4 * d < L) {b : ℝ} (hb : 0 < b) (hbd : b < d)
    (hf : PolyhedralPLInCharts e f D2)
    (hcompat : ∀ k l, (e k).symm.trans (e l) ∈ piecewiseAffineGroupoid V3)
    (hfR : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hdis : Disjoint (closure (G.collar 0).outer.inside)
      (closure (G.collar 1).outer.inside)) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ EqOn g f Q2 ∧
      MapsTo g D2 R ∧ (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      ∀ Z : Set X, (∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) →
        Disjoint (G.tube '' _root_.Dehn.identityTube L d) Z →
        (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧
          IsFinitePLBallPair V2 D2 (D2 ∩ g ⁻¹' Z) := by
  classical
  let B := fun b : Bool => G.collar (if b then 1 else 0)
  let P := fun b => (B b).outer
  let I := fun b => (B b).inner
  let c := fun b => (B b).regionChart
  let S := fun b => closure (I b).inside
  let C := fun b => closure (P b).inside \ (I b).inside
  let O := D2 \ ((P false).inside ∪ (P true).inside)
  have hP b := (B b).outer_simplicial
  have hPi b := (B b).outer_injective
  have hI b := (B b).inner_simplicial
  have hIi b := (B b).inner_injective
  have hPsq b : (P b).boundary ℝ ⊆ ball 0 1 :=
    (G.boundaries_interior (if b then 1 else 0)).1
  have hIsq b : (I b).boundary ℝ ⊆ ball 0 1 :=
    (G.boundaries_interior (if b then 1 else 0)).2
  have hn b := (B b).nested
  obtain ⟨hcover, hseamI, hseamP, hdisI, hdisIO, hdisC, hdisIC, hclosedC,
      hclosedO, hSball, hCball, hrim⟩ :=
    _root_.Dehn.disjoint_annulus_source_partition P I hP hPi hI hIi hPsq hn hdis
  have hpre : D2 ∩ f ⁻¹' (G.tube '' _root_.Dehn.identityTube L d) = C false ∪ C true := by
    rw [G.full_preimage, (G.collar 0).carrier, (G.collar 1).carrier]
    rfl
  have htouter : (C false ∪ C true) ∩ O =
      (P false).boundary ℝ ∪ (P true).boundary ℝ := by
    rw [union_inter_distrib_right, hseamP false, hseamP true]
  have htinner (b : Bool) : (C false ∪ C true) ∩ S b = (I b).boundary ℝ := by
    have hother : C (!b) ∩ S b = ∅ :=
      (disjoint_left.mpr (fun x hx hy =>
        disjoint_left.mp (hdisIC (!b)) (by cases b <;> exact hy) hx)).inter_eq
    cases b
    · change C true ∩ S false = ∅ at hother
      rw [union_inter_distrib_right, hother, union_empty, inter_comm, hseamI false]
    · change C false ∩ S true = ∅ at hother
      rw [union_inter_distrib_right, hother, empty_union, inter_comm, hseamI true]
  obtain ⟨eb, heb, houter, hinner⟩ := G.exists_disjoint_boundary_data hd hwidth
  obtain ⟨H, js, a, g, hH, hjs, hjsH, hjsImage, hjsInv, hjsBoundary,
      ha, hadis, hg, hglocal, hgcompact, hkeep, hout, hgr, hcollar,
      hresolved, himage, hcross, hpreimage, hproper⟩ :=
    _root_.Dehn.exists_disjoint_resolved_annuli_map e hcompat P I hP hPi hI hIi
      hPsq hIsq hn hdis eb heb hd hwidth hb hbd c
      (fun b => (B b).regionChart_PL) (fun b => (B b).outer_depth)
      (fun b => (B b).inner_depth) f hf old.isLocallyInjective
      G.tube G.tube_PL G.tube_fibers houter hinner (C false ∪ C true) hpre htouter htinner
  have hkeep0 (x : S false) : g (H x) = f x := by
    rw [← show js true x = (H x : V2) from hjsH true x]
    exact hkeep true x x.property
  have hkeep1 (x : S true) : g (H.symm x) = f x := by
    rw [← show js false x = (H.symm x : V2) from hjsH false x]
    exact hkeep false x x.property
  obtain ⟨j, facts, hjrange, hj0, hj1, hjO, hjPL⟩ :=
    _root_.Dehn.exists_disjoint_retained_fibers P I hP hPi hI hIi hPsq hn hdis H hH c
      f g a (fun b => (ha b).1.injective) hadis hkeep0 hkeep1 hout hcollar hcross
  obtain ⟨hwhole, _, _, hiK, _, havoid⟩ := G.disjoint_retention hd hdis
  obtain ⟨Hopen⟩ := _root_.Dehn.disjoint_retained_open_source_restriction
    P I hP hPi hI hIi hPsq hn hdis H hH j facts hjrange hj0 hj1 hjO
      (fun x hx hd => disjoint_left.mp havoid ⟨hx, hd⟩)
  obtain ⟨hmodel, hboundary, hinterior⟩ := facts.ordinary_circle_resolution old
    hf.continuousOn hg.continuousOn hjPL Hopen hwhole i (G.selected_disjoint_rim 0) hiK
  have hasub (k : Bool) : a k '' squareAnnulus L d ⊆
      G.tube '' _root_.Dehn.identityTube L d := by
    rintro z ⟨p, hp, rfl⟩
    let q : squareAnnulus L d := ⟨p, hp⟩
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth q
    let u : Icc (-d) d := ⟨depth L q, mem_squareAnnulus_iff_depth.mp hp⟩
    have hv := hresolved k s hs u
    rw [← hsp] at hv
    refine ⟨((u, signedHeight b k u), s), ?_, hv.symm⟩
    exact _root_.Dehn.identity_strip_mapsTo hbd.le k (x := (s, (u : ℝ))) ⟨hs, u.property⟩
  have htR : G.tube '' _root_.Dehn.identityTube L d ⊆ R :=
    image_subset_iff.mpr (G.tube_interior.mono_right interior_subset)
  have hgR : MapsTo g D2 R := by
    intro x hx
    rcases himage.subset (mem_image_of_mem g hx) with ((hx0 | hx1) | hxo) | (ha0 | ha1)
    · obtain ⟨y, hy, heq⟩ := hx0
      exact heq ▸ hfR (ball_subset_closedBall (hSball false hy))
    · obtain ⟨y, hy, heq⟩ := hx1
      exact heq ▸ hfR (ball_subset_closedBall (hSball true hy))
    · obtain ⟨y, hy, heq⟩ := hxo
      exact heq ▸ hfR hy.1
    · exact htR (hasub false ha0)
    · exact htR (hasub true ha1)
  have htfront : Disjoint (G.tube '' _root_.Dehn.identityTube L d) (frontier R) :=
    disjoint_left.mpr (fun z hz hzfront => by
      obtain ⟨w, hw, rfl⟩ := hz
      exact disjoint_left.mp disjoint_interior_frontier (G.tube_interior hw) hzfront)
  exact ⟨g, hg, hgr, hgR, (hproper (frontier R) hfront htfront).1,
    hmodel, hboundary, hinterior, hproper⟩


theorem exists_disjoint_circle_resolution [T2Space X] (G : PairedCircleCollars D L d)
    (hd : 0 < d) (hwidth : 4 * d < L) {b : ℝ} (hb : 0 < b) (hbd : b < d)
    (hf : PolyhedralPLInCharts e f D2)
    (hcompat : ∀ k l, (e k).symm.trans (e l) ∈ piecewiseAffineGroupoid V3)
    (hfR : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (hdis : Disjoint (closure (G.collar 0).outer.inside)
      (closure (G.collar 1).outer.inside)) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  obtain ⟨g, hg, hrim, hin, hfront, hmodel, hboundary, hinterior, _⟩ :=
    G.exists_disjoint_step hd hwidth hb hbd hf hcompat hfR hfront hdis
  exact ⟨g, hg, hin, hrim, hfront, hboundary, hinterior, hmodel⟩

end PoincareConjecture.M76.Dehn.PairedCircleCollars
