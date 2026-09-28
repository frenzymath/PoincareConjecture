import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.BoundaryCorrespondence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedResolvedAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.LocalInjectivity











set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.PairedCircleCollars

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

theorem exists_nested_insertion (G : PairedCircleCollars D L d)
    (hd : 0 < d) (hwidth : 4 * d < L) {b : ℝ} (hb : 0 < b) (hbd : b < d)
    (hf : PolyhedralPLInCharts e f D2)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (j : Fin 2)
    (hnest : closure (G.collar j.rev).outer.inside ⊆ (G.collar j).inner.inside) :
    let P := (G.collar j).outer
    let I := (G.collar j).inner
    let Q := (G.collar j.rev).inner
    let c := (G.collar j).regionChart
    ∃ (H : closure Q.inside ≃ₜ closure I.inside) (J : V2 → V2)
      (a : P2 → X) (g : V2 → X),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn J (closure Q.inside) ∧
      (∀ x : closure Q.inside, J x = (H x : V2)) ∧
      J '' closure Q.inside = closure I.inside ∧
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      PolyhedralPLInCharts e g D2 ∧ IsLocallyInjective (fun x : D2 ↦ g x) ∧
      (∀ x ∈ closure Q.inside, g (J x) = f x) ∧
      EqOn g f (D2 \ P.inside) ∧ EqOn g f Q2 ∧
      (∀ p : squareAnnulus L d, g (c p) = a p) ∧
      g '' D2 = (f '' closure Q.inside ∪ f '' (D2 \ P.inside)) ∪
        a '' squareAnnulus L d ∧
      (∀ x ∈ closure P.inside \ I.inside,
        ∀ y ∈ closure I.inside ∪ (D2 \ P.inside), g x = g y ↔ x = y) ∧
      (∀ W : Set X, D2 ∩ g ⁻¹' W =
        (J '' (closure Q.inside ∩ f ⁻¹' W) ∪ ((D2 \ P.inside) ∩ f ⁻¹' W)) ∪
          (fun p : squareAnnulus L d ↦ (c p : V2)) '' {p | a p ∈ W}) ∧
      (∀ Z : Set X, (∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) →
        Disjoint (G.tube '' _root_.Dehn.identityTube L d) Z →
        (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧ IsFinitePLBallPair V2 D2 (D2 ∩ g ⁻¹' Z)) ∧
      IsFinitePLBallPair V2 D2 Q2 ∧
      a '' squareAnnulus L d ⊆ G.tube '' _root_.Dehn.identityTube L d ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          G.tube (_root_.Dehn.nestedTubeReindex j ((u, max |(u : ℝ)| b), s)) := by
  let P := (G.collar j).outer
  let I := (G.collar j).inner
  let Q := (G.collar j.rev).inner
  let c := (G.collar j).regionChart
  let tau := G.tube ∘ _root_.Dehn.nestedTubeReindex j
  have hQI : closure Q.inside ⊆ I.inside :=
    (G.collar j.rev).nested.trans (subset_closure.trans hnest)
  obtain ⟨eb, heb, _, heval, _⟩ :=
    _root_.Dehn.exists_synchronized_collar_boundary_homeomorph Q I
      (G.collar j.rev).inner_simplicial (G.collar j.rev).inner_injective
      (G.collar j.rev).boundary_subset_source.2 (G.collar j).boundary_subset_source.2
      (G.collar j.rev).chart (G.collar j).chart
      (G.collar j.rev).chart_PL (G.collar j).chart_PL
      (G.collar j.rev).inner_depth (G.collar j).inner_depth
  obtain ⟨htau, himage, htauFib⟩ := _root_.Dehn.nestedTubeReindex_map e G.length_pos hd
    j G.tube G.tube_PL G.tube_fibers
  have houter (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d)
      (hp : (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) :
      f (c p) = tau ((-d, d), s) := by
    change f ((G.collar j).chart p) = _
    rw [G.period_value j s hs ⟨-d, by constructor <;> linarith⟩ p hp]
    exact congrArg G.tube (_root_.Dehn.nestedTubeReindex_corners j d s).1.symm
  have hinner (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (p : squareAnnulus L d)
      (x : Q.boundary ℝ)
      (hp : (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), d))
      (hx : (eb x : V2) = c p) : f x = tau ((d, d), s) := by
    have heq := (heval x).symm.trans hx
    have hparam : (G.collar j.rev).chart.symm
        ⟨x, (G.collar j.rev).boundary_subset_source.2 x.property⟩ = p :=
      (G.collar j).chart.injective (Subtype.ext heq)
    have hxp : (x : V2) = (G.collar j.rev).chart p := by
      rw [← hparam, (G.collar j.rev).chart.apply_symm_apply]
    rw [hxp, G.period_value j.rev s hs ⟨d, by constructor <;> linarith⟩ p hp]
    exact congrArg G.tube (_root_.Dehn.nestedTubeReindex_corners j d s).2.symm
  have hpre : D2 ∩ f ⁻¹' (tau '' _root_.Dehn.identityTube L d) =
      G.source 0 ∪ G.source 1 := by
    rw [himage]
    exact G.full_preimage
  obtain ⟨hout, hin⟩ := G.nested_contacts j hnest
  obtain ⟨H, J, a, g, hH, hJ, hJH, hJb, hJimage, haemb, haPL, hgPL, hglocal,
    hglocalEmb, hJvalue, houtside, hrim, hcollar, hperiod, hfullimage, hcross,
    hpreimage, hproper, hball⟩ :=
    _root_.Dehn.exists_nested_resolved_annulus_map e hcompat P I Q
      (G.collar j).outer_simplicial (G.collar j).outer_injective
      (G.collar j).inner_simplicial (G.collar j).inner_injective
      (G.collar j.rev).inner_simplicial (G.collar j.rev).inner_injective
      (G.boundaries_interior j).1 (G.boundaries_interior j).2
      (G.boundaries_interior j.rev).2 (G.collar j).nested hQI eb heb hd hwidth hb hbd
      c (G.collar j).regionChart_PL (G.collar j).outer_depth (G.collar j).inner_depth
      f hf old.isLocallyInjective tau htau htauFib houter hinner
      (G.source 0 ∪ G.source 1) hpre hout hin
  have hasub : a '' squareAnnulus L d ⊆ G.tube '' _root_.Dehn.identityTube L d := by
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p, hp⟩
    let u : Icc (-d) d := ⟨depth L p, mem_squareAnnulus_iff_depth.mp hp⟩
    have hval : a p = tau (((u : ℝ), max |(u : ℝ)| b), s) :=
      (congrArg a hsp).trans (hperiod s hs u)
    apply himage.subset
    refine ⟨(((u : ℝ), max |(u : ℝ)| b), s), ?_, hval.symm⟩
    exact ⟨⟨u.property, ⟨by linarith [le_max_left |(u : ℝ)| b, abs_nonneg (u : ℝ)],
      max_le (abs_le.mpr u.property) hbd.le⟩⟩, hs⟩
  exact ⟨H, J, a, g, hH, hJ, hJH, hJimage, haemb, haPL, hgPL, hglocal,
    hJvalue, houtside, hrim, hcollar, hfullimage, hcross, hpreimage,
    fun Z hfZ hdis ↦ hproper Z hfZ (himage.symm ▸ hdis), hball, hasub, hperiod⟩

end PoincareConjecture.M76.Dehn.PairedCircleCollars
