import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.Pullback

/-!
# Null-set preservation by the actual polar strip

The positive Jacobian transfers every almost-everywhere property. This
lets the actual weak tangent columns descend to almost every circle.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

/-- The positive actual polar Jacobian preserves every supplied almost-everywhere disk
property. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64MorreyPolarStrip_ae (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho)
    {q : LoopPlane → Prop} (hq : ∀ᵐ p ∂volume.restrict (Metric.closedBall a rho), q p) :
    ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain), q (m64MorreyPolarStrip a rho p) := by
  classical
  let F : LoopPlane → ℝ := fun p => if q p then 0 else 1
  have hzero : F =ᵐ[volume.restrict (Metric.closedBall a rho)] (fun _ => (0 : ℝ)) :=
    hq.mono (fun p hp => by simp only [F, if_pos hp])
  have hi : IntegrableOn F (Metric.closedBall a rho) volume :=
    (integrable_zero _ _ _).congr hzero.symm
  have hpos : ∀ p, 0 ≤ F p := by intro p; dsimp [F]; split_ifs <;> norm_num
  have hz : (∫ p in Metric.closedBall a rho, F p) = 0 := by
    simpa only [integral_zero] using integral_congr_ae hzero
  have hp := m64MorreyPolarStrip_integrable a hrho hi
  have hb := m64MorreyPolarStrip_integral_le a hrho hi hpos
  rw [hz, mul_zero] at hb
  have hpi : (∫ p in interior m64AnnulusDomain, F (m64MorreyPolarStrip a rho p)) = 0 :=
    le_antisymm hb (integral_nonneg (fun p => hpos _))
  have hpae := (integral_eq_zero_iff_of_nonneg (fun p => hpos _) hp).mp hpi
  filter_upwards [hpae] with p hp0
  by_contra hnot
  simp only [F, if_neg hnot, Pi.zero_apply, one_ne_zero] at hp0

end PoincareMT
