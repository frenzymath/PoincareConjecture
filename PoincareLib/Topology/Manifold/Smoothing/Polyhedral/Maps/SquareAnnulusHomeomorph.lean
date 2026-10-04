import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.SquareAnnulusInjectivity
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual square-annulus homeomorphism

The continuous circle-band parametrization is injective and
has the exact square-annulus range. Compactness supplies its
continuous inverse, with the actual map and its fixed middle
rectangle retained. See Hatcher p. 7, Hamilton 1976, p. 66 and
M76 derivation 270.
-/

set_option autoImplicit false

open Set Topology

namespace PLAnnularStrip

/-- The explicit four-strip circle map gives a homeomorphism
onto the literal square annulus. Zero width is allowed here;
later two-dimensional charts require positive width. See
Hatcher p. 7 and M76 derivation 270. -/
theorem exists_annulus_homeomorph {L d : ℝ}
    (hL : 0 < L) (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    ∃ e : (AddCircle (4 * L) × Icc (-d) d) ≃ₜ squareAnnulus L d,
      ∀ p, (e p : ℝ × ℝ) = annulusMap L hL (p.1, p.2) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have he := (continuous_annulusMap hd hwidth).isClosedEmbedding
    (injective_annulusMap hL hwidth)
  exact ⟨he.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_annulusMap hL hd hwidth)), fun _ => rfl⟩

/-- The actual annulus homeomorphism retains every point of
the middle rectangle where both corner corrections vanish.
This is the fixed overlap used for two crossing bands. See
Hatcher p. 7 and M76 derivation 270. -/
theorem exists_core_fixed_annulus_homeomorph {L d : ℝ}
    (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    ∃ e : (AddCircle (4 * L) × Icc (-d) d) ≃ₜ squareAnnulus L d,
      (∀ p, (e p : ℝ × ℝ) = annulusMap L (by linarith) (p.1, p.2)) ∧
      ∀ (s : ℝ) (t : Icc (-d) d), 2 * |(t : ℝ)| ≤ s →
        2 * |(t : ℝ)| ≤ L - s →
        (e ((s : AddCircle (4 * L)), t) : ℝ × ℝ) = (s, (t : ℝ)) := by
  obtain ⟨e, he⟩ := exists_annulus_homeomorph (by linarith) hd hwidth
  refine ⟨e, he, ?_⟩
  intro s t hleft hright
  rw [he]
  exact annulusMap_middle (by linarith)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr t.property)
      (by norm_num)) hwidth) hleft hright

end PLAnnularStrip
