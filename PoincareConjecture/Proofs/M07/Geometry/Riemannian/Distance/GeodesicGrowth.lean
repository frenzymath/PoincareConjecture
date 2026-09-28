import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal

namespace PoincareConjecture

variable {X : Type*} [EMetricSpace X]



theorem edist_prefix_eq_of_remainder_eq
    {γ : ℝ → X} {p q : X} {D : ℝ} (hD : 0 ≤ D)
    (h0 : γ 0 = p) (hpq : edist p q = ENNReal.ofReal D)
    (hupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist (γ s) (γ t) ≤ ENNReal.ofReal (|s - t| * D))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hrem : edist (γ t) q = ENNReal.ofReal ((1 - t) * D)) :
    ∀ s ∈ Icc (0 : ℝ) t,
      edist p (γ s) = ENNReal.ofReal (s * D) ∧
      edist (γ s) q = ENNReal.ofReal ((1 - s) * D) := by
  intro s hs
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
  have hleft : edist p (γ s) ≤ ENNReal.ofReal (s * D) := by
    simpa only [h0, zero_sub, abs_neg, abs_of_nonneg hs.1] using
      hupper 0 (by simp) s hs1
  have hright : edist (γ s) q ≤ ENNReal.ofReal ((1 - s) * D) := by
    calc
      edist (γ s) q ≤ edist (γ s) (γ t) + edist (γ t) q := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal ((t - s) * D) + ENNReal.ofReal ((1 - t) * D) := by
        apply add_le_add
        · simpa only [abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using
            hupper s hs1 t ht
        · exact hrem.le
      _ = ENNReal.ofReal ((1 - s) * D) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hs.2) hD)
          (mul_nonneg (sub_nonneg.mpr ht.2) hD)]
        congr 1
        ring
  have hsum : ENNReal.ofReal (s * D) + ENNReal.ofReal ((1 - s) * D) ≤
      edist p (γ s) + edist (γ s) q := by
    rw [← ENNReal.ofReal_add (mul_nonneg hs.1 hD)
      (mul_nonneg (sub_nonneg.mpr hs1.2) hD)]
    rw [show s * D + (1 - s) * D = D by ring, ← hpq]
    exact edist_triangle _ _ _
  constructor
  · apply le_antisymm hleft
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp
      (hsum.trans (add_le_add le_rfl hright))
  · apply le_antisymm hright
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp
      (hsum.trans (add_le_add hleft le_rfl))




theorem edist_segment_of_local_growth
    {γ : ℝ → X} {p q : X} {D : ℝ} (hD : 0 ≤ D)
    (h0 : γ 0 = p) (hpq : edist p q = ENNReal.ofReal D)
    (hupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist (γ s) (γ t) ≤ ENNReal.ofReal (|s - t| * D))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc (0 : ℝ) 1)
    (hinit : edist (γ t₀) q = ENNReal.ofReal ((1 - t₀) * D))
    (hstep : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∀ s ∈ Icc (0 : ℝ) t,
        edist p (γ s) = ENNReal.ofReal (s * D) ∧
        edist (γ s) q = ENNReal.ofReal ((1 - s) * D)) →
      ∃ u ∈ Ioc t 1, edist (γ u) q = ENNReal.ofReal ((1 - u) * D)) :
    γ 1 = q ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist (γ s) (γ t) = ENNReal.ofReal (|s - t| * D) := by
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.continuousOn (K := ⟨D, hD⟩)
    intro s hs t ht
    have h := hupper s hs t ht
    rw [ENNReal.ofReal_mul (abs_nonneg _)] at h
    rw [← ENNReal.ofReal_coe_nnreal]
    change edist (γ s) (γ t) ≤ ENNReal.ofReal D * edist s t
    rw [edist_dist, Real.dist_eq, mul_comm]
    exact h
  let S : Set ℝ := {t | edist (γ t) q = ENNReal.ofReal ((1 - t) * D)}
  have hsub : Icc t₀ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left ht₀.1.le
  have hclosed : IsClosed (S ∩ Icc t₀ 1) := by
    have h := isClosed_Icc.isClosed_eq
      (show ContinuousOn (fun t => edist (γ t) q) (Icc t₀ 1) from
        fun t ht => ((hcont.mono hsub) t ht).tendsto.edist tendsto_const_nhds)
      (show ContinuousOn (fun t : ℝ => ENNReal.ofReal ((1 - t) * D)) (Icc t₀ 1) by
        exact (ENNReal.continuous_ofReal.comp
          ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn)
    convert h using 1
    ext x
    simp only [S, mem_inter_iff, mem_ofPred_eq, and_comm]
  have hlast : (1 : ℝ) ∈ S := hclosed.mem_of_ge_of_forall_exists_gt hinit ht₀.2
    (fun t ht => by
      obtain ⟨u, hu, hurem⟩ := hstep t ⟨ht₀.1.trans_le ht.2.1, ht.2.2⟩
        (edist_prefix_eq_of_remainder_eq hD h0 hpq hupper
          ⟨ht₀.1.le.trans ht.2.1, ht.2.2.le⟩ ht.1)
      exact ⟨u, hurem, hu⟩)
  have h1 : γ 1 = q := by
    apply edist_eq_zero.mp
    simpa only [S, mem_ofPred_eq, sub_self, zero_mul, ENNReal.ofReal_zero] using hlast
  have hprefix := edist_prefix_eq_of_remainder_eq hD h0 hpq hupper
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hlast
  have hforward : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      edist (γ s) (γ t) = ENNReal.ofReal (|s - t| * D) := by
    intro s hs t ht hst
    apply le_antisymm (hupper s hs t ht)
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    apply (ENNReal.add_le_add_iff_left (a := ENNReal.ofReal (s * D))
      ENNReal.ofReal_ne_top).mp
    apply (ENNReal.add_le_add_iff_right (a := ENNReal.ofReal ((1 - t) * D))
      ENNReal.ofReal_ne_top).mp
    have hbudget : (ENNReal.ofReal (s * D) + ENNReal.ofReal ((t - s) * D)) +
        ENNReal.ofReal ((1 - t) * D) = ENNReal.ofReal D := by
      rw [← ENNReal.ofReal_add (mul_nonneg hs.1 hD)
        (mul_nonneg (sub_nonneg.mpr hst) hD),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hs.1 hD)
          (mul_nonneg (sub_nonneg.mpr hst) hD))
          (mul_nonneg (sub_nonneg.mpr ht.2) hD)]
      congr 1
      ring
    rw [hbudget, ← hpq, ← (hprefix s hs).1, ← (hprefix t ht).2]
    exact (edist_triangle p (γ s) q).trans
      ((add_le_add le_rfl (edist_triangle (γ s) (γ t) q)).trans_eq (add_assoc _ _ _).symm)
  refine ⟨h1, fun s hs t ht => ?_⟩
  rcases le_total s t with hst | hts
  · exact hforward s hs t ht hst
  · simpa only [edist_comm, abs_sub_comm] using hforward t ht s hs hts

end PoincareConjecture
