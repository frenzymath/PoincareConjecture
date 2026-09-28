import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryContinuousReflection
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace PoincareConjecture

def m64BoundaryThinStrip (R h : ℝ) : Set LoopPlane :=
  {p | p 0 ∈ Icc 0 h ∧ p 1 ∈ Icc (-R) R}

theorem m64BoundaryThinStrip_measurableSet (R h : ℝ) :
    MeasurableSet (m64BoundaryThinStrip R h) := by
  exact ((isClosed_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).inter
    (isClosed_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous)).measurableSet

theorem m64BoundaryThinStrip_volume (R h : ℝ) :
    volume (m64BoundaryThinStrip R h) = ENNReal.ofReal h * ENNReal.ofReal (2 * R) := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let q : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp _
  have hq : MeasurePreserving q volume volume := volume_preserving_finTwoArrow ℝ
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) h ×ˢ Icc (-R) R
  have hK : NullMeasurableSet K volume := by measurability
  have hpre := (hq.comp he).measure_preimage hK
  have heq : (q ∘ e) ⁻¹' K = m64BoundaryThinStrip R h := by
    ext p
    simp [q, e, K, m64BoundaryThinStrip, MeasurableEquiv.finTwoArrow_apply,
      and_assoc, and_left_comm]
  rw [heq] at hpre
  rw [hpre]
  dsimp only [K]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring

theorem m64BoundaryThinStrip_volume_ne_top (R h : ℝ) :
    volume (m64BoundaryThinStrip R h) ≠ ⊤ := by
  rw [m64BoundaryThinStrip_volume]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem m64BoundaryThinStrip_volume_real {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) :
    volume.real (m64BoundaryThinStrip R h) = 2 * R * h := by
  rw [Measure.real, m64BoundaryThinStrip_volume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hh, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem m64Continuous_zero_trace_uniform_small {u : LoopPlane → ℝ}
    (hu : Continuous u) (hc : HasCompactSupport u)
    (hzero : ∀ p : LoopPlane, p 0 = 0 → u p = 0) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p : LoopPlane, |p 0| < delta → ‖u p‖ < epsilon := by
  obtain ⟨delta, hd, hclose⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hu) epsilon he
  refine ⟨delta, hd, ?_⟩
  intro p hp
  let q := p - p 0 • (EuclideanSpace.single 0 1 : LoopPlane)
  have hq : q 0 = 0 := by simp [q]
  have hdist : dist p q = |p 0| := by
    simp [q, norm_smul, Real.norm_eq_abs]
  have hh := hclose (show dist p q < delta from hdist ▸ hp)
  simpa only [hzero q hq, dist_zero_right] using hh

end PoincareConjecture
