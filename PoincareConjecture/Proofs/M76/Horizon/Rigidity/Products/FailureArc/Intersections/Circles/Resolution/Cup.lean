import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.CupEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.UnpushedAnnulus

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_circle_cup
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {A₀ A₁ : Set P2} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (f₀ f₁ : P2 → X)
    (hf : PolyhedralPLInCharts e f₁ (closure B₁.inner.inside))
    (hfi : InjOn f₁ (closure B₁.inner.inside))
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    {A B : Set X} (hinnerA : f₁ '' closure B₁.inner.inside ⊆ A)
    (hinnerB : Disjoint (f₁ '' closure B₁.inner.inside) B)
    (hA : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ A ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ B ↔ z.1.2 = -z.1.1)
    (houter : ∀ p : squareAnnulus L d, depth L p = -d →
      ∀ s ∈ Icc 0 (4 * L), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d) →
        f₀ (B₀.chart p) = τ ((-d, d), s))
    (hinner : ∀ p : squareAnnulus L d, depth L p = d →
      ∀ s ∈ Icc 0 (4 * L), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), d) →
        f₁ (B₁.chart p) = τ ((d, d), s)) :
    ∃ v : P2 → X,
      PolyhedralPLInCharts e v (closure B₀.outer.inside) ∧
      IsEmbedding (fun x : closure B₀.outer.inside ↦ v x) ∧
      EqOn v f₀ (B₀.outer.boundary ℝ) ∧
      (v '' closure B₀.outer.inside) ∩ A = f₁ '' closure B₁.inner.inside ∧
      (v '' closure B₀.outer.inside) ∩ B = f₀ '' B₀.outer.boundary ℝ ∧
      v '' closure B₀.outer.inside = f₁ '' closure B₁.inner.inside ∪
        τ '' ((Icc (-d) d ×ˢ {d}) ×ˢ Icc 0 (4 * L)) := by
  obtain ⟨a, hai, ha, hperiod, haimage, haA, haB⟩ :=
    exists_unpushed_cap_annulus e hcompat hd hwidth τ hτ hfib hA hB
  have haouter (p : squareAnnulus L d) (hp : depth L p = -d) : a p = f₀ (B₀.chart p) := by
    obtain ⟨s, hs, hv⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hp] at hv
    have hh := hperiod s hs ⟨-d, le_rfl, by linarith⟩
    rw [← hv] at hh
    exact hh.trans (houter p hp s hs hv).symm
  have hainner (p : squareAnnulus L d) (hp : depth L p = d) : a p = f₁ (B₁.chart p) := by
    obtain ⟨s, hs, hv⟩ := exists_period_parameter_of_depth hd hwidth p
    rw [hp] at hv
    have hh := hperiod s hs ⟨d, by linarith, le_rfl⟩
    rw [← hv] at hh
    exact hh.trans (hinner p hp s hs hv).symm
  obtain ⟨H, v, _, hv, hvi, hva, hHperiod, himage⟩ :=
    exists_cup_map e hcompat B₀ B₁ f₁ a hf ha hainner
  have hvinj := cup_map_injective B₀ B₁ H hfi hai.injective hvi hva hHperiod hainner
    (fun p hp ↦ (haA p p.property).mp (hinnerA hp))
  let : CompactSpace (closure B₀.outer.inside) := isCompact_iff_compactSpace.mp
    (B₀.outer.isFinitePLBallPair_closed_inside B₀.outer_simplicial B₀.outer_injective).isCompact
  have hkeep : EqOn v f₀ (B₀.outer.boundary ℝ) := by
    intro x hx
    have hxA := (oriented_collar_boundary_subsets B₀).1 hx
    let p := B₀.chart.symm ⟨x, hxA⟩
    have hp : (B₀.chart p : P2) = x := congrArg Subtype.val (B₀.chart.apply_symm_apply _)
    rw [← hp, hva]
    exact haouter p ((B₀.outer_depth p).mp (hp.symm ▸ hx))
  have hcapA : (v '' closure B₀.outer.inside) ∩ A = f₁ '' closure B₁.inner.inside := by
    rw [himage, union_inter_distrib_right, inter_eq_left.mpr hinnerA]
    apply union_eq_left.mpr
    rintro _ ⟨⟨p, hp, rfl⟩, hpA⟩
    have hpd := (haA p hp).mp hpA
    exact ⟨B₁.chart ⟨p, hp⟩,
      (B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective).1
        ((B₁.inner_depth _).mpr hpd), (hainner ⟨p, hp⟩ hpd).symm⟩
  have hcapB : (v '' closure B₀.outer.inside) ∩ B = f₀ '' B₀.outer.boundary ℝ := by
    rw [himage, union_inter_distrib_right, hinnerB.inter_eq, empty_union]
    ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hpB⟩
      have hpd := (haB p hp).mp hpB
      exact ⟨B₀.chart ⟨p, hp⟩, (B₀.outer_depth _).mpr hpd, (haouter ⟨p, hp⟩ hpd).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxA := (oriented_collar_boundary_subsets B₀).1 hx
      let p := B₀.chart.symm ⟨x, hxA⟩
      have hp : (B₀.chart p : P2) = x := congrArg Subtype.val (B₀.chart.apply_symm_apply _)
      have hpd := (B₀.outer_depth p).mp (hp.symm ▸ hx)
      have hpv : a p = f₀ x := (haouter p hpd).trans (congrArg f₀ hp)
      exact ⟨⟨p, p.property, hpv⟩, hpv ▸ (haB p p.property).mpr hpd⟩
  exact ⟨v, hv, (hv.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hh ↦ Subtype.ext (hvinj x.property y.property hh))).isEmbedding,
      hkeep, hcapA, hcapB, himage.trans (congrArg _ haimage)⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
