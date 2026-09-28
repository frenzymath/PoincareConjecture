import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_BadSamples
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_ScalarMargin
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M45

structure GluingBadSequence (epsilon : ℝ) where
  beta : ℕ → ℝ
  beta_pos : ∀ n, 0 < beta n
  beta_le_quarter : ∀ n, beta n ≤ 1 / 4
  beta_tendsto_zero : Tendsto beta atTop (𝓝 0)
  input : ∀ n, M45NeckGluingInput.{u} epsilon (beta n)
  tolerance_lt_half : ∀ n, beta n * epsilon < 1 / 2
  recent_short : ∀ n, (input n).recent_duration < 1
  scale_gt_one : ∀ n, 1 < (input n).older_neck.neck.scale ^ 2
  scale_lt_four : ∀ n, (input n).older_neck.neck.scale ^ 2 < 4
  older_survival : ∀ n, 1 < (input n).older_duration
  time : ℕ → ℝ
  time_mem : ∀ n, time n ∈ Ioc (-1 : ℝ) 0
  time_older : ∀ n, time n < -(input n).recent_duration
  point : ℕ → RoundCylinderSpace
  point_mem : ∀ n, (point n).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹
  bad : ∀ n, epsilon ^ 2 / 2 < roundCylinderJetErrorSquared (time n)
    ((input n).piecewiseTensor (input n).recent_patch.coordinate (time n))
    ⌊epsilon⁻¹⌋₊ (point n)

def GluingBadSequence.subseq {epsilon : ℝ} (S : GluingBadSequence.{u} epsilon)
    (f : ℕ → ℕ) (hf : StrictMono f) : GluingBadSequence.{u} epsilon where
  beta := S.beta ∘ f
  beta_pos n := S.beta_pos (f n)
  beta_le_quarter n := S.beta_le_quarter (f n)
  beta_tendsto_zero := S.beta_tendsto_zero.comp hf.tendsto_atTop
  input n := S.input (f n)
  tolerance_lt_half n := S.tolerance_lt_half (f n)
  recent_short n := S.recent_short (f n)
  scale_gt_one n := S.scale_gt_one (f n)
  scale_lt_four n := S.scale_lt_four (f n)
  older_survival n := S.older_survival (f n)
  time := S.time ∘ f
  time_mem n := S.time_mem (f n)
  time_older n := S.time_older (f n)
  point := S.point ∘ f
  point_mem n := S.point_mem (f n)
  bad n := S.bad (f n)

theorem exists_gluing_bad_sequence {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hnot : ¬ ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 2 ∧
      M45NeckGluingProperty.{u} epsilon beta) : Nonempty (GluingBadSequence.{u} epsilon) := by
  classical
  obtain ⟨eta0, heta0, hquarter, hscale⟩ := exists_short_input_scale_bounds.{u}
  let b := min (1 / 4) (eta0 / epsilon)
  have hb : 0 < b := lt_min (by norm_num) (div_pos heta0 hepsilon)
  let beta (n : ℕ) : ℝ := b / ((n : ℝ) + 1)
  have hbeta (n : ℕ) : 0 < beta n := by dsimp [beta]; positivity
  have hbetab (n : ℕ) : beta n ≤ b := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hbetaquarter (n : ℕ) : beta n ≤ 1 / 4 := (hbetab n).trans (min_le_left _ _)
  have hbetasmall (n : ℕ) : beta n * epsilon ≤ eta0 := by
    exact (mul_le_mul_of_nonneg_right (hbetab n) hepsilon.le).trans
      ((le_div_iff₀ hepsilon).mp (min_le_right _ _))
  have hhalf (n : ℕ) : beta n * epsilon < 1 / 2 :=
    lt_of_le_of_lt ((hbetasmall n).trans hquarter) (by norm_num)
  have hbetalim : Tendsto beta atTop (𝓝 0) := by
    simpa only [beta, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul b
  have hexists (n : ℕ) : ∃ I : M45NeckGluingInput.{u} epsilon (beta n),
      ¬ Nonempty (M45NeckGluingConclusion I) := by
    apply not_forall.mp
    intro h
    exact hnot ⟨beta n, hbeta n, lt_of_le_of_lt (hbetaquarter n) (by norm_num), h⟩
  choose I hfail using hexists
  have hshort (n : ℕ) : (I n).recent_duration < 1 := by
    by_contra hn
    exact hfail n (gluingConclusion_of_recent_duration hepsilon (hbeta n)
      (by linarith [hbetaquarter n]) (hhalf n) (I n) (le_of_not_gt hn))
  have hs (n : ℕ) := hscale (I n) (mul_pos (hbeta n) hepsilon) (hbetasmall n) (hshort n)
  have hsample (n : ℕ) := exists_bad_older_sample hepsilon (hbeta n)
    (by linarith [hbetaquarter n]) (hhalf n) (I n) (hs n).2.2.2.2.le (hfail n)
  choose t ht htold z hz hbad using hsample
  exact ⟨{
    beta := beta
    beta_pos := hbeta
    beta_le_quarter := hbetaquarter
    beta_tendsto_zero := hbetalim
    input := I
    tolerance_lt_half := hhalf
    recent_short := hshort
    scale_gt_one := fun n => (hs n).2.2.1
    scale_lt_four := fun n => (hs n).2.2.2.1
    older_survival := fun n => (hs n).2.2.2.2
    time := t
    time_mem := ht
    time_older := htold
    point := z
    point_mem := hz
    bad := hbad
  }⟩

theorem exists_gluing_bad_sequence_duration_limit {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hnot : ¬ ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 2 ∧
      M45NeckGluingProperty.{u} epsilon beta) :
    ∃ S : GluingBadSequence.{u} epsilon, ∃ d ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => (S.input n).recent_duration) atTop (𝓝 d) := by
  obtain ⟨S⟩ := exists_gluing_bad_sequence hepsilon hnot
  obtain ⟨d, hd, f, hf, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq
    (fun n => ⟨(S.input n).recent_duration_pos.le, (S.recent_short n).le⟩)
  exact ⟨S.subseq f hf, d, hd, hlim⟩

end PoincareConjecture.M45
