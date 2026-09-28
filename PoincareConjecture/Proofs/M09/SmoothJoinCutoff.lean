import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

noncomputable def smoothJoinCutoff (s : ℝ) : ℝ :=
  Real.smoothTransition ((s + 1) / 2)

theorem smoothJoinCutoff_contDiff : ContDiff ℝ ∞ smoothJoinCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const 2)

theorem smoothJoinCutoff_mem (s : ℝ) : smoothJoinCutoff s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem smoothJoinCutoff_zero {s : ℝ} (hs : s ≤ -1) : smoothJoinCutoff s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem smoothJoinCutoff_one {s : ℝ} (hs : 1 ≤ s) : smoothJoinCutoff s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem smoothJoinCutoff_hasDerivAt (c d s : ℝ) :
    HasDerivAt (fun t ↦ smoothJoinCutoff ((t - c) / d))
      (deriv smoothJoinCutoff ((s - c) / d) / d) s := by
  have h : HasDerivAt smoothJoinCutoff (deriv smoothJoinCutoff ((s - c) / d))
      ((s - c) / d) := (smoothJoinCutoff_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  simpa only [Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using
    h.comp s (((hasDerivAt_id s).sub_const c).div_const d)

theorem exists_smoothJoinCutoff_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖deriv smoothJoinCutoff s‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (smoothJoinCutoff_contDiff.continuous_deriv (by simp)).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun s hs ↦ (hC s hs).trans (le_max_left _ _)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def smoothJoinBlend (f g : ℝ → E) (c d s : ℝ) : E :=
  f s + smoothJoinCutoff ((s - c) / d) • (g s - f s)

theorem smoothJoinBlend_eq_left (f g : ℝ → E) (c : ℝ) {d s : ℝ}
    (hd : 0 < d) (hs : s ≤ c - d) : smoothJoinBlend f g c d s = f s := by
  have h : (s - c) / d ≤ -1 := (div_le_iff₀ hd).mpr (by linarith)
  simp only [smoothJoinBlend, smoothJoinCutoff_zero h, zero_smul, add_zero]

theorem smoothJoinBlend_eq_right (f g : ℝ → E) (c : ℝ) {d s : ℝ}
    (hd : 0 < d) (hs : c + d ≤ s) : smoothJoinBlend f g c d s = g s := by
  have h : 1 ≤ (s - c) / d := (le_div_iff₀ hd).mpr (by linarith)
  simp only [smoothJoinBlend, smoothJoinCutoff_one h, one_smul, add_sub_cancel]

theorem smoothJoinBlend_mem_convex (f g : ℝ → E) (c d s : ℝ)
    (K : Set E) (hK : Convex ℝ K) (hf : f s ∈ K) (hg : g s ∈ K) :
    smoothJoinBlend f g c d s ∈ K := by
  apply hK.add_smul_mem hf (by simpa only [add_sub_cancel] using hg)
  exact smoothJoinCutoff_mem _

theorem smoothJoinBlend_contDiffOn (f g : ℝ → E) (c d : ℝ) (U : Set ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (smoothJoinBlend f g c d) U :=
  hf.add ((smoothJoinCutoff_contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const d)).contDiffOn.smul (hg.sub hf))

theorem smoothJoinBlend_hasDerivAt (f g : ℝ → E) (c d s : ℝ)
    (hf : DifferentiableAt ℝ f s) (hg : DifferentiableAt ℝ g s) :
    HasDerivAt (smoothJoinBlend f g c d)
      (deriv f s + (deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s) +
        smoothJoinCutoff ((s - c) / d) • (deriv g s - deriv f s)) s := by
  convert! hf.hasDerivAt.add ((smoothJoinCutoff_hasDerivAt c d s).smul
    (hg.hasDerivAt.sub hf.hasDerivAt)) using 1 <;>
    simp only [smoothJoinBlend, Pi.sub_apply, add_assoc, add_comm, add_left_comm]

theorem exists_smoothJoinBlend_uniform_deriv_bound (f g : ℝ → E)
    (U : Set ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (c r : ℝ) (hr : 0 < r) (hI : Set.Icc (c - r) (c + r) ⊆ U) (heq : f c = g c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d, 0 < d → d ≤ r → ∀ s ∈ Set.Icc (c - d) (c + d),
      ‖deriv (smoothJoinBlend f g c d) s‖ ≤ C := by
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((hf.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).mono hI)
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((hg.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn).mono hI)
  let C := max (max Cf Cg) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hfC (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : ‖deriv f s‖ ≤ C :=
    (hCf s hs).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hgC (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : ‖deriv g s‖ ≤ C :=
    (hCg s hs).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hfd (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : DifferentiableAt ℝ f s :=
    (hf.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)
  have hgd (s : ℝ) (hs : s ∈ Set.Icc (c - r) (c + r)) : DifferentiableAt ℝ g s :=
    (hg.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)
  obtain ⟨K, hK, hKb⟩ := exists_smoothJoinCutoff_deriv_bound
  refine ⟨3 * C + K * (2 * C), by positivity, ?_⟩
  intro d hd hdr s hs
  have hsI : s ∈ Set.Icc (c - r) (c + r) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcI : c ∈ Set.Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have habs : ‖s - c‖ ≤ d := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hcoord : (s - c) / d ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨(le_div_iff₀ hd).mpr (by linarith [hs.1]),
      (div_le_iff₀ hd).mpr (by linarith [hs.2])⟩
  have hfg : ‖g s - f s‖ ≤ 2 * C * d := by
    have hfL := (convex_Icc (c - r) (c + r)).norm_image_sub_le_of_norm_deriv_le
      hfd hfC hcI hsI
    have hgL := (convex_Icc (c - r) (c + r)).norm_image_sub_le_of_norm_deriv_le
      hgd hgC hcI hsI
    have he : g s - f s = (g s - g c) - (f s - f c) := by rw [heq]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (by nlinarith [hfL, hgL, mul_le_mul_of_nonneg_left habs hC])
  have hchi : ‖smoothJoinCutoff ((s - c) / d)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (smoothJoinCutoff_mem _).1]
    exact (smoothJoinCutoff_mem _).2
  have hKD : ‖deriv smoothJoinCutoff ((s - c) / d) / d‖ ≤ K / d := by
    rw [norm_div, Real.norm_of_nonneg hd.le]
    exact div_le_div_of_nonneg_right (hKb _ hcoord) hd.le
  have hterm : ‖(deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s)‖ ≤ K * (2 * C) := by
    rw [norm_smul]
    calc
      _ ≤ (K / d) * (2 * C * d) := mul_le_mul hKD hfg (norm_nonneg _) (div_nonneg hK hd.le)
      _ = K * (2 * C) := by field_simp [hd.ne']
  have hlast : ‖smoothJoinCutoff ((s - c) / d) • (deriv g s - deriv f s)‖ ≤ 2 * C := by
    rw [norm_smul]
    calc
      _ ≤ 1 * (‖deriv g s‖ + ‖deriv f s‖) :=
        mul_le_mul hchi (norm_sub_le _ _) (norm_nonneg _) zero_le_one
      _ ≤ 2 * C := by linarith [hfC s hsI, hgC s hsI]
  rw [(smoothJoinBlend_hasDerivAt f g c d s (hfd s hsI) (hgd s hsI)).deriv]
  exact (norm_add_le _ _).trans (by
    have hsum := norm_add_le (deriv f s)
      ((deriv smoothJoinCutoff ((s - c) / d) / d) • (g s - f s))
    linarith [hfC s hsI, hterm, hlast])

end PoincareConjecture.Proofs.M09
