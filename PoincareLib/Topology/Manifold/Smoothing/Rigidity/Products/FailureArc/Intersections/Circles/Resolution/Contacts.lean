import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.TransverseAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Circles.AnnulusBoundaryParameters
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Circles.SourceAnnulusPeriod

/-! # Whole-surface contacts of the separated cap collar -/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_cap_annulus_with_contacts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d ε : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hε : 0 < ε) (hεd : ε < 2 * d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    {A B : Set X}
    (hA : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ A ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ B ↔ z.1.2 = -z.1.1) :
    ∃ g : P2 → X,
      Topology.IsEmbedding (fun x : squareAnnulus L d ↦ g x) ∧
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          τ (capStrip d ε (s, u))) ∧
      Disjoint (g '' squareAnnulus L d) A ∧
      (∀ x ∈ squareAnnulus L d, g x ∈ B ↔ depth L x = -d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) = τ ((-d, d), s) ∧
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) = τ ((d - ε, d), s)) ∧
      (g '' squareAnnulus L d) ∩ B = (fun s : ℝ ↦ τ ((-d, d), s)) '' Icc 0 (4 * L) := by
  obtain ⟨g, hgi, hg, hperiod, himage, hends⟩ :=
    exists_transverse_cap_annulus e hcompat hd hwidth hε.le hεd τ hτ hfib
  have havoid : Disjoint (g '' squareAnnulus L d) A := by
    rw [himage]
    apply disjoint_left.mpr
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩ ha
    have hdiag := (hA _ (capStrip_mapsTo hd hε.le hεd hp)).mp ha
    exact (ne_of_lt (capStrip_avoids_diagonal hd hε hεd hp)) hdiag.symm
  have hproper (x : P2) (hx : x ∈ squareAnnulus L d) : g x ∈ B ↔ depth L x = -d := by
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth (⟨x, hx⟩ : squareAnnulus L d)
    let u : Icc (-d) d := ⟨depth L x, mem_squareAnnulus_iff_depth.mp hx⟩
    have hv := hperiod s hs u
    rw [← hsp] at hv
    rw [hv, hB _ (capStrip_mapsTo hd hε.le hεd ⟨hs, u.property⟩),
      capStrip_antidiagonal_iff hd hεd]
  refine ⟨g, hgi, hg, hperiod, havoid, hproper, hends, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth (⟨x, hx⟩ : squareAnnulus L d)
    have hdpt := (hproper x hx).mp hy
    refine ⟨s, hs, ?_⟩
    have hv := (hends s hs).1
    rw [hdpt] at hsp
    rw [← hsp] at hv
    exact hv.symm
  · rintro ⟨s, hs, rfl⟩
    let u : Icc (-d) d := ⟨-d, le_rfl, by linarith⟩
    have hmem := _root_.Dehn.annulus_period_point_mem hd hwidth s u
    refine ⟨⟨_, hmem, (hends s hs).1⟩, ?_⟩
    apply (hB _ ?_).mpr (by simp)
    exact ⟨⟨⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩, hs⟩

end PoincareMT.M76.Dehn.Annuli.CircleResolution
