import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricRayRegularity
import Mathlib.Topology.MetricSpace.Completion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem intrinsic_end_ray_eq_after_interior
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) {a t0 : ℝ} {gamma sigma : ℝ → U},
      t0 ∈ Ioo (0 : ℝ) a →
      sigma 0 = gamma t0 →
      (∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
        dist (gamma s) (gamma t) = |s - t|) →
      (∀ s ∈ Ico (0 : ℝ) (a - t0), ∀ t ∈ Ico (0 : ℝ) (a - t0),
        dist (sigma s) (sigma t) = |s - t|) →
      (∀ s ∈ Ico (0 : ℝ) a,
        dist (gamma s : UniformSpace.Completion U) E = a - s) →
      (∀ s ∈ Ico (0 : ℝ) (a - t0),
        dist (sigma s : UniformSpace.Completion U) E = a - t0 - s) →
      ∀ s ∈ Ico (0 : ℝ) (a - t0), sigma s = gamma (t0 + s) := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E a t0 gamma sigma ht0 hstart hgamma hsigma hgammaRadius hsigmaRadius
  let tau : ℝ → U := fun t => if t ≤ t0 then gamma t else sigma (t - t0)
  have hleft (t : ℝ) (ht : t ≤ t0) : tau t = gamma t := by
    simp only [tau, if_pos ht]
  have hright (t : ℝ) (ht : t0 < t) : tau t = sigma (t - t0) := by
    simp only [tau, if_neg (not_le.mpr ht)]
  have ht0ray : t0 ∈ Ico (0 : ℝ) a := ⟨ht0.1.le, ht0.2⟩
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (a - t0) :=
    ⟨le_rfl, sub_pos.mpr ht0.2⟩
  have hshift (t : ℝ) (ht : t ∈ Ico (0 : ℝ) a) (ht0t : t0 < t) :
      t - t0 ∈ Ico (0 : ℝ) (a - t0) :=
    ⟨(sub_pos.mpr ht0t).le, sub_lt_sub_right ht.2 t0⟩
  have hlipschitz (x y : U) :
      dist (x : UniformSpace.Completion U) E -
        dist (y : UniformSpace.Completion U) E ≤ dist x y := by
    have h := dist_triangle (x : UniformSpace.Completion U)
      (y : UniformSpace.Completion U) E
    rw [UniformSpace.Completion.dist_eq] at h
    linarith
  have hcross (s : ℝ) (hs : s ∈ Ico (0 : ℝ) a)
      (t : ℝ) (ht : t ∈ Ico (0 : ℝ) a) (hst0 : s ≤ t0) (ht0t : t0 < t) :
      dist (tau s) (tau t) = |s - t| := by
    have htshift := hshift t ht ht0t
    have hleg1 : dist (gamma s) (gamma t0) = t0 - s := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr hst0), neg_sub] using
        hgamma s hs t0 ht0ray
    have hleg2 : dist (gamma t0) (sigma (t - t0)) = t - t0 := by
      simpa only [hstart, zero_sub, abs_neg, abs_of_nonneg htshift.1] using
        hsigma 0 hzero (t - t0) htshift
    have hupper := dist_triangle (gamma s) (gamma t0) (sigma (t - t0))
    rw [hleg1, hleg2] at hupper
    have hlower := hlipschitz (gamma s) (sigma (t - t0))
    rw [hgammaRadius s hs, hsigmaRadius (t - t0) htshift] at hlower
    rw [hleft s hst0, hright t ht0t,
      abs_of_nonpos (sub_nonpos.mpr (hst0.trans ht0t.le)), neg_sub]
    linarith
  have htau : ∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
      dist (tau s) (tau t) = |s - t| := by
    intro s hs t ht
    by_cases hst0 : s ≤ t0
    · by_cases htt0 : t ≤ t0
      · rw [hleft s hst0, hleft t htt0]
        exact hgamma s hs t ht
      · exact hcross s hs t ht hst0 (lt_of_not_ge htt0)
    · have ht0s : t0 < s := lt_of_not_ge hst0
      by_cases htt0 : t ≤ t0
      · rw [dist_comm, abs_sub_comm]
        exact hcross t ht s hs htt0 ht0s
      · have ht0t : t0 < t := lt_of_not_ge htt0
        rw [hright s ht0s, hright t ht0t,
          hsigma (s - t0) (hshift s hs ht0s) (t - t0) (hshift t ht ht0t)]
        congr 1
        ring
  have hgammaGeo := (intrinsic_metric_ray_regular g U hfinite hgamma).1
  have htauGeo := (intrinsic_metric_ray_regular g U hfinite htau).1
  have hmid : t0 / 2 ∈ Ioo (0 : ℝ) a :=
    ⟨half_pos ht0.1, (half_lt_self ht0.1).trans ht0.2⟩
  have hnear : gamma =ᶠ[𝓝 (t0 / 2)] tau := by
    filter_upwards [Ioo_mem_nhds (half_pos ht0.1) (half_lt_self ht0.1)] with t ht
    exact (hleft t ht.2.le).symm
  have heq := hgammaGeo.eqOn_of_eq_nhds htauGeo
    (convex_Ioo (0 : ℝ) a).isPreconnected hmid hnear
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    simpa only [add_zero] using hstart
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have htime : t0 + s ∈ Ioo (0 : ℝ) a := by
      constructor <;> linarith [ht0.1, hs.2]
    have h := heq htime
    rw [hright (t0 + s) (by linarith), add_sub_cancel_left] at h
    exact h.symm

end PoincareConjecture.M28
