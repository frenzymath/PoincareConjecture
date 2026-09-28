import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.EntropyTraceContinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2V" => Lp V 2 (volume : Measure V)

theorem raw_volumeDensity_pos (g : RiemannianMetric n V) (x : V) :
    0 < g.pullbackVolumeDensity id x := by
  rw [raw_volumeDensity_eq]
  exact Real.sqrt_pos.mpr (rawCoordinateGram_posDef g x).det_pos

theorem metricEntropyPotential_nonneg (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ∀ x, 0 ≤ η x) (Q : ℝ) (x z : V) :
    0 ≤ metricEntropyPotential g η Q (x, z) :=
  mul_nonneg (mul_nonneg (hη x) (raw_volumeDensity_pos g x).le) (normBoundEntropy_nonneg _ _)

theorem metricEntropy_zero_of_norm_bound (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) (u : L2V)
    (hb : ∀ᵐ x ∂volume, g.inner x (u x) (u x) ≤ Q) :
    fieldIntegral (metricEntropyPotential g η Q) u = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hb] with x hx
  simp only [metricEntropyPotential, normBoundEntropy_zero_of_le hx, mul_zero, Pi.zero_apply]

theorem metric_norm_bound_of_entropy_zero (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x) {K : Set V} (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : L2V)
    (hzero : fieldIntegral (metricEntropyPotential g η Q) u = 0) :
    ∀ᵐ x ∂volume, x ∈ K → g.inner x (u x) (u x) ≤ Q := by
  have hz : (fun x => metricEntropyPotential g η Q (x, u x)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => metricEntropyPotential_nonneg g hη0 Q x (u x))
      (metricEntropyPotential_integrable g hη hc hQ u)).mp hzero
  filter_upwards [hz] with x hx
  intro hxK
  apply (normBoundEntropy_eq_zero_iff Q _).mp
  have he : g.pullbackVolumeDensity id x * normBoundEntropy Q (g.inner x (u x) (u x)) = 0 := by
    simpa only [metricEntropyPotential, hηK x hxK, one_mul, Pi.zero_apply] using hx
  exact (mul_eq_zero.mp he).resolve_left (raw_volumeDensity_pos g x).ne'

theorem metricEntropy_trace_eq_zero {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x) {Q : ℝ} (hQ : 0 ≤ Q)
    (U : ℝ → L2V) (hU : ContinuousOn U (Icc a b))
    (hinit : ∀ᵐ x ∂volume, (F.metric a).inner x (U a x) (U a x) ≤ Q)
    (hdec : ∀ t ∈ Ioo a b, ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt
      (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U s)) d t) :
    ∀ t ∈ Icc a b, fieldIntegral (metricEntropyPotential (F.metric t) η Q) (U t) = 0 := by
  have hcont := metricEntropy_trace_continuousOn F isCompact_Icc hJ hη hc hQ U hU
  have hdiff : DifferentiableOn ℝ
      (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U s))
      (interior (Icc a b)) := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨d, _, hd⟩ := hdec t ht
    exact hd.differentiableAt.differentiableWithinAt
  have hnonpos : ∀ t ∈ interior (Icc a b),
      deriv (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U s)) t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨d, hd, hder⟩ := hdec t ht
    exact hder.deriv.symm ▸ hd
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff hnonpos
  have hzero := metricEntropy_zero_of_norm_bound (F.metric a) η Q (U a) hinit
  intro t ht
  apply le_antisymm
  · exact (hanti ⟨le_rfl, hab⟩ ht ht.1).trans_eq hzero
  · exact integral_nonneg fun x => metricEntropyPotential_nonneg (F.metric t) hη0 Q x (U t x)

end PoincareConjecture.M35.Uniqueness.Heat
