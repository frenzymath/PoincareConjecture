import PoincareConjecture.Proofs.M32.Claim11_35.FiniteSlabs

set_option autoImplicit false

open Set Filter
open scoped ENNReal Topology

universe u

namespace PoincareConjecture.M32

noncomputable def restrictControlledBlowupCylinderTime
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T T' B eta : ℝ}
    (e : ControlledBlowupCylinder S k A T B eta) (h : T' ≤ T) :
    ControlledBlowupCylinder S k A T' B eta := by
  have hI : Icc (-T') 0 ⊆ Icc (-T) 0 := Icc_subset_Icc (neg_le_neg h) le_rfl
  exact {
    embedding := restrictCylinderTime e.embedding hI
    zero_identity := fun hs x hx => e.zero_identity (hI hs) x hx
    curvature_bound := fun s hs x hx => e.curvature_bound s (hI hs) x hx
    negative_curvature_bound := fun s hs x hx => e.negative_curvature_bound s (hI hs) x hx }

theorem geometricLongControls_of_closed_cylinders
    (S : GeneralizedBlowupSequence.{u}) {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hcompact : BlowupBaseBallsCompact S)
    (hvolume : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (S.scale k)) ^ 3) ≤
        calibratedMetricVolume ((S.flow k).metric (S.base k).1) (S.baseBall k rho))
    (hcyl : ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop,
      Nonempty (ControlledBlowupCylinder S k A T B eta)) :
    M30GeometricLongControls S (ENNReal.ofReal T) where
  horizon_pos := ENNReal.ofReal_pos.mpr hT
  balls_compact := hcompact
  terminal_volume := hvolume
  cylinders t _ht hbelow := by
    have htT : t ≤ T := (ENNReal.ofReal_lt_ofReal_iff hT).mp hbelow |>.le
    refine ⟨B, hB, ?_⟩
    intro A hA eta heta
    exact (hcyl A hA eta heta).mono fun _ hk =>
      hk.map fun e => restrictControlledBlowupCylinderTime e htT

end PoincareConjecture.M32
