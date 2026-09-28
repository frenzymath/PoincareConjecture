import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {x : X}



theorem closure_ball_eq_closedBall_of_approximate_radial_projection
    (hproject : ∀ R r ε : ℝ, 0 ≤ r → r ≤ R → 0 < ε →
      closedBall x R ⊆ thickening (R - r + ε) (closedBall x r))
    {r : ℝ} (hr : 0 < r) : closure (ball x r) = closedBall x r := by
  apply Subset.antisymm closure_ball_subset_closedBall
  intro y hy
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let s := max 0 (r - ε / 2)
  have hs : 0 ≤ s := le_max_left _ _
  have hsr : s < r := max_lt hr (by linarith)
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp
    (hproject r s (ε / 2) hs hsr.le (half_pos hε) hy)
  refine ⟨z, hz.trans_lt hsr, hyz.trans_le ?_⟩
  have hgap : r - ε / 2 ≤ s := le_max_right _ _
  linarith

variable [ProperSpace X]




theorem continuousOn_sSup_image_closedBall_of_approximate_radial_projection
    (hproject : ∀ R r ε : ℝ, 0 ≤ r → r ≤ R → 0 < ε →
      closedBall x R ⊆ thickening (R - r + ε) (closedBall x r))
    {f : X → ℝ} (hf : Continuous f) :
    ContinuousOn (fun r : ℝ => sSup (f '' closedBall x r)) (Ici 0) := by
  let S := fun r : ℝ => sSup (f '' closedBall x r)
  have hb (r : ℝ) : BddAbove (f '' closedBall x r) :=
    (isCompact_closedBall x r).bddAbove_image hf.continuousOn
  intro r hr
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall x (r + 1)).uniformContinuousOn_of_continuous
      hf.continuousOn) (ε / 2) (half_pos hε)
  have hcompare (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hsR : s ≤ r + 1) (htR : t ≤ r + 1) (hst : |t - s| < δ / 4) :
      S t < S s + ε / 2 := by
    obtain ⟨y, hy, hSy⟩ := (isCompact_closedBall x t).exists_sSup_image_eq
      ⟨x, mem_closedBall_self ht⟩ hf.continuousOn
    have hyR : y ∈ closedBall x (r + 1) := closedBall_subset_closedBall htR hy
    by_cases hts : t ≤ s
    · have hys : y ∈ closedBall x s := closedBall_subset_closedBall hts hy
      have hle : f y ≤ S s := le_csSup (hb s) (mem_image_of_mem f hys)
      dsimp [S]
      rw [hSy]
      dsimp [S] at hle
      linarith
    · have hst' : s ≤ t := le_of_lt (lt_of_not_ge hts)
      obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp
        (hproject t s (δ / 4) hs hst' (by positivity) hy)
      have hzR : z ∈ closedBall x (r + 1) := closedBall_subset_closedBall hsR hz
      have hd : dist y z < δ := by
        have hd' := (abs_lt.mp hst).2
        linarith
      have hv := hδf y hyR z hzR hd
      rw [Real.dist_eq] at hv
      have hle : f z ≤ S s := le_csSup (hb s) (mem_image_of_mem f hz)
      change sSup (f '' closedBall x t) < S s + ε / 2
      rw [hSy]
      have hsmall := (abs_lt.mp hv).2
      linarith
  refine ⟨min (1 / 2) (δ / 4), by positivity, ?_⟩
  intro s hs hsr
  rw [Real.dist_eq] at hsr
  have hsmall := lt_of_lt_of_le hsr (min_le_right _ _)
  have hsR : s ≤ r + 1 := by
    have hhalf := (abs_lt.mp (lt_of_lt_of_le hsr (min_le_left _ _))).2
    linarith
  have h1 := hcompare r s hr hs (by linarith) hsR hsmall
  have h2 := hcompare s r hs hr hsR (by linarith) (by simpa only [abs_sub_comm] using hsmall)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  change -ε < S s - S r ∧ S s - S r < ε
  constructor <;> linarith



theorem sSup_image_ball_eq_closedBall_of_approximate_radial_projection
    (hproject : ∀ R r ε : ℝ, 0 ≤ r → r ≤ R → 0 < ε →
      closedBall x R ⊆ thickening (R - r + ε) (closedBall x r))
    {f : X → ℝ} (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    sSup (f '' ball x r) = sSup (f '' closedBall x r) := by
  have hb : BddAbove (f '' closedBall x r) :=
    (isCompact_closedBall x r).bddAbove_image hf.continuousOn
  have hbo : BddAbove (f '' ball x r) := hb.mono (image_mono ball_subset_closedBall)
  have hlo : ∀ y ∈ ball x r, f y ≤ sSup (f '' ball x r) :=
    fun y hy => le_csSup hbo (mem_image_of_mem f hy)
  have hcl : closedBall x r ⊆ {y | f y ≤ sSup (f '' ball x r)} := by
    rw [← closure_ball_eq_closedBall_of_approximate_radial_projection hproject hr]
    exact closure_minimal hlo (isClosed_le hf continuous_const)
  apply le_antisymm
  · exact csSup_le ⟨f x, mem_image_of_mem f (mem_ball_self hr)⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      exact le_csSup hb (mem_image_of_mem f (ball_subset_closedBall hy)))
  · exact csSup_le ⟨f x, mem_image_of_mem f (mem_closedBall_self hr.le)⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      exact hcl hy)

end Metric
