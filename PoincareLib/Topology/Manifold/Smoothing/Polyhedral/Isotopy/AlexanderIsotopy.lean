import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homotopy.Basic

/-!
# Alexander isotopy for a homeomorphism of bounded displacement

Conjugating a homeomorphism by shrinking dilations gives a jointly continuous
family through the identity if its displacement is uniformly bounded. The
same holds for the inverse family. This is the Alexander isotopy used in
Hamilton 1976, proof of Theorem 1, pp. 66, 68. See M76 derivation 10.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dilation conjugate at nonzero time, completed by the identity at zero.
See Hamilton 1976, pp. 66, 68, and M76 derivation 10. -/
noncomputable def alexanderFamily (e : E ≃ₜ E) (t : ℝ) : E ≃ₜ E := by
  classical
  exact if ht : t = 0 then Homeomorph.refl E else
    (Homeomorph.smulOfNeZero t ht).symm.trans (e.trans (Homeomorph.smulOfNeZero t ht))

/-- The Alexander family starts at the identity, by definition at the singular
scaling parameter. See M76 derivation 10. -/
@[simp] theorem alexanderFamily_zero (e : E ≃ₜ E) :
    e.alexanderFamily 0 = Homeomorph.refl E := by
  simp [alexanderFamily]

/-- Away from zero the family is the usual Alexander scaling formula.
See Hamilton p. 68 and M76 derivation 10. -/
theorem alexanderFamily_apply_of_ne_zero (e : E ≃ₜ E) {t : ℝ} (ht : t ≠ 0) (x : E) :
    e.alexanderFamily t x = t • e (t⁻¹ • x) := by
  simp [alexanderFamily, ht]

/-- At time one the family is the given homeomorphism.
See M76 derivation 10. -/
@[simp] theorem alexanderFamily_one (e : E ≃ₜ E) : e.alexanderFamily 1 = e := by
  ext x
  simp [alexanderFamily_apply_of_ne_zero e one_ne_zero]

/-- Inversion commutes with the Alexander construction.
See M76 derivation 10. -/
theorem alexanderFamily_symm (e : E ≃ₜ E) (t : ℝ) :
    (e.alexanderFamily t).symm = e.symm.alexanderFamily t := by
  by_cases ht : t = 0
  · simp [ht]
  · ext x
    simp [alexanderFamily, ht]

/-- A uniform displacement bound shrinks by the absolute value of time.
This is the continuity estimate in M76 derivation 10, for Hamilton p. 68. -/
theorem norm_alexanderFamily_sub_le (e : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖e x - x‖ ≤ C) (t : ℝ) (x : E) :
    ‖e.alexanderFamily t x - x‖ ≤ ‖t‖ * C := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [e.alexanderFamily_apply_of_ne_zero ht]
    calc
      ‖t • e (t⁻¹ • x) - x‖ = ‖t • (e (t⁻¹ • x) - t⁻¹ • x)‖ := by
        rw [smul_sub, smul_inv_smul₀ ht]
      _ = ‖t‖ * ‖e (t⁻¹ • x) - t⁻¹ • x‖ := norm_smul _ _
      _ ≤ ‖t‖ * C := mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- Uniformly bounded displacement gives joint continuity through time zero.
See the Alexander isotopy of Hamilton pp. 66, 68, and M76 derivation 10. -/
theorem continuous_alexanderFamily (e : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖e x - x‖ ≤ C) :
    Continuous (fun p : ℝ × E => e.alexanderFamily p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have hnorm : Tendsto (fun q : ℝ × E => ‖q.1‖ * C) (𝓝 p) (𝓝 0) := by
      simpa [hp] using (continuous_fst.norm.mul_const C).continuousAt.tendsto (x := p)
    have hdelta : Tendsto (fun q : ℝ × E => e.alexanderFamily q.1 q.2 - q.2)
        (𝓝 p) (𝓝 0) :=
      squeeze_zero_norm (fun q => e.norm_alexanderFamily_sub_le hC q.1 q.2) hnorm
    simpa [ContinuousAt, hp] using hdelta.add continuous_snd.continuousAt
  · have hformula : ContinuousAt (fun q : ℝ × E => q.1 • e (q.1⁻¹ • q.2)) p :=
      continuous_fst.continuousAt.smul (e.continuous.continuousAt.comp
        ((continuous_fst.continuousAt.inv₀ hp).smul continuous_snd.continuousAt))
    apply hformula.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually_ne hp] with q hq
    exact e.alexanderFamily_apply_of_ne_zero hq q.2

/-- The inverse family is jointly continuous under the same displacement
bound. See M76 derivation 10 and Hamilton p. 68. -/
theorem continuous_alexanderFamily_symm (e : E ≃ₜ E) {C : ℝ}
    (hC : ∀ x, ‖e x - x‖ ≤ C) :
    Continuous (fun p : ℝ × E => (e.alexanderFamily p.1).symm p.2) := by
  have hsymm : ∀ x, ‖e.symm x - x‖ ≤ C := by
    intro x
    rw [norm_sub_rev]
    simpa only [e.apply_symm_apply] using hC (e.symm x)
  simpa only [alexanderFamily_symm] using e.symm.continuous_alexanderFamily hsymm

end Homeomorph
