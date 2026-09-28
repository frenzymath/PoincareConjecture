import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Model
import Mathlib.Topology.Compactness.Compact









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.SingularRegularLimit

open RiemannianMetric



theorem exists_modelVolume_ratio_margin {κ ρ L : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) :
    ∃ cmax : ℝ, 1 < cmax ∧ ∀ c : ℝ, 1 < c → c < cmax →
      ∀ r ∈ Icc ρ L,
        (3 / 4 : ℝ) * c ^ 6 < modelVolume 3 κ (r / c ^ 2) / modelVolume 3 κ r := by
  have hevent : ∀ᶠ c : ℝ in 𝓝 1, ∀ r ∈ Icc ρ L,
      (3 / 4 : ℝ) * c ^ 6 < modelVolume 3 κ (r / c ^ 2) / modelVolume 3 κ r := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hrpos : 0 < r := hρ.trans_le hr.1
    have hnum : ContinuousAt (fun p : ℝ × ℝ => modelVolume 3 κ (p.2 / p.1 ^ 2)) (1, r) :=
      (continuous_modelVolume 3 κ).continuousAt.comp
        (continuousAt_snd.div (continuousAt_fst.pow 2) (by norm_num))
    have hden : ContinuousAt (fun p : ℝ × ℝ => modelVolume 3 κ p.2) (1, r) :=
      (continuous_modelVolume 3 κ).continuousAt.comp continuousAt_snd
    have hcont := hnum.div hden (modelVolume_pos (by norm_num) hκ hrpos).ne'
    have hleft : ContinuousAt (fun p : ℝ × ℝ => (3 / 4 : ℝ) * p.1 ^ 6) (1, r) :=
      continuousAt_const.mul (continuousAt_fst.pow 6)
    have hvalue : (3 / 4 : ℝ) * (1 : ℝ) ^ 6 -
        modelVolume 3 κ (r / (1 : ℝ) ^ 2) / modelVolume 3 κ r < 0 := by
      simp only [one_pow, mul_one, div_one, div_self
        (modelVolume_pos (n := 3) (by norm_num) hκ hrpos).ne']
      norm_num
    simpa only [Pi.sub_apply, Pi.div_apply, sub_lt_zero] using
      (hleft.sub hcont).eventually (Iio_mem_nhds hvalue)
  obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨1 + δ / 2, by linarith, ?_⟩
  intro c hc hcmax
  apply hclose
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hc)]
  linarith

end PoincareConjecture.SingularRegularLimit
