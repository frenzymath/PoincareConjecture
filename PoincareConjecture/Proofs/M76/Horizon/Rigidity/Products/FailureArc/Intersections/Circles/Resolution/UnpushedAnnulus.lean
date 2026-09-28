import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.TransverseAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusBoundaryParameters
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_unpushed_cap_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    {A B : Set X}
    (hA : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ A ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ B ↔ z.1.2 = -z.1.1) :
    ∃ a : P2 → X,
      Topology.IsEmbedding (fun x : squareAnnulus L d ↦ a x) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) = τ ((u, d), s)) ∧
      a '' squareAnnulus L d = τ '' ((Icc (-d) d ×ˢ {d}) ×ˢ Icc 0 (4 * L)) ∧
      (∀ x ∈ squareAnnulus L d, a x ∈ A ↔ depth L x = d) ∧
      (∀ x ∈ squareAnnulus L d, a x ∈ B ↔ depth L x = -d) := by
  obtain ⟨a, hai, ha, hp, himage, _⟩ := exists_transverse_cap_annulus e hcompat hd hwidth
    (show (0 : ℝ) ≤ 0 by rfl) (show (0 : ℝ) < 2 * d by positivity) τ hτ hfib
  have hperiod (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) = τ ((u, d), s) := by
    simpa [capStrip] using hp s hs u
  have hparam (x : P2) (hx : x ∈ squareAnnulus L d) :
      ∃ s ∈ Icc 0 (4 * L), a x = τ ((depth L x, d), s) := by
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth (⟨x, hx⟩ : squareAnnulus L d)
    have hv := hperiod s hs ⟨depth L x, mem_squareAnnulus_iff_depth.mp hx⟩
    rw [← hsp] at hv
    exact ⟨s, hs, hv⟩
  have hmem (x : P2) (hx : x ∈ squareAnnulus L d) (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) :
      ((depth L x, d), s) ∈ _root_.Dehn.identityTube L d :=
    ⟨⟨mem_squareAnnulus_iff_depth.mp hx, ⟨by linarith, le_rfl⟩⟩, hs⟩
  refine ⟨a, hai, ha, hperiod, ?_, ?_, ?_⟩
  · rw [himage]
    congr 1
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [capStrip] using And.intro (And.intro hp.2 (show d ∈ ({d} : Set ℝ) from rfl)) hp.1
    · rintro ⟨⟨hu, hd'⟩, hs⟩
      refine ⟨(z.2, z.1.1), ⟨hs, hu⟩, ?_⟩
      have hv : z.1.2 = d := hd'
      simp only [capStrip, zero_div, sub_zero, one_mul]
      exact Prod.ext (Prod.ext rfl hv.symm) rfl
  · intro x hx
    obtain ⟨s, hs, hv⟩ := hparam x hx
    rw [hv, hA _ (hmem x hx s hs)]
    exact eq_comm
  · intro x hx
    obtain ⟨s, hs, hv⟩ := hparam x hx
    rw [hv, hB _ (hmem x hx s hs)]
    change d = -depth L x ↔ depth L x = -d
    constructor <;> intro hh <;> linarith

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
