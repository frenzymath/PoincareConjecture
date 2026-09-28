import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalGrowth
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactWeakChain










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.M60

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace




theorem suNormalizedCoefficient_full_bound
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : P × (ℝ × E) → F) (x : P) (v : E) {t C : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (degree : ℝ)
    (hN : DifferentiableAt ℝ N (x, t, t • v))
    (hC : ‖fderiv ℝ N (x, t, t • v)‖ ≤ C) :
    DifferentiableAt ℝ (fun z : P × E => t ^ degree • N (z.1, t, t • z.2)) (x, v) ∧
      ‖fderiv ℝ (fun z : P × E => t ^ degree • N (z.1, t, t • z.2)) (x, v)‖ ≤
        C * t ^ degree := by
  let L : (P × E) →L[ℝ] P × (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ P E).prod
      ((0 : (P × E) →L[ℝ] ℝ).prod (t • ContinuousLinearMap.snd ℝ P E))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro z
    change max ‖z.1‖ (max ‖(0 : ℝ)‖ ‖t • z.2‖) ≤ 1 * ‖z‖
    simp only [Prod.norm_def, norm_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, one_mul]
    exact max_le (le_max_left _ _) (max_le (by positivity)
      ((mul_le_mul_of_nonneg_right ht1 (norm_nonneg z.2)).trans (by simp)))
  have harg : HasFDerivAt (fun z : P × E => (z.1, t, t • z.2)) L (x, v) :=
    hasFDerivAt_fst.prodMk
      ((hasFDerivAt_const t (x, v)).prodMk (hasFDerivAt_snd.const_smul t))
  have hd := (hN.hasFDerivAt.comp (x, v) harg).const_smul (t ^ degree)
  change HasFDerivAt (fun z : P × E => t ^ degree • N (z.1, t, t • z.2))
    (t ^ degree • (fderiv ℝ N (x, t, t • v)).comp L) (x, v) at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
  calc
    _ ≤ t ^ degree * (‖fderiv ℝ N (x, t, t • v)‖ * ‖L‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
        (Real.rpow_nonneg ht.le _)
    _ ≤ t ^ degree * (C * 1) := mul_le_mul_of_nonneg_left
      (mul_le_mul hC hL (norm_nonneg L) ((norm_nonneg _).trans hC))
      (Real.rpow_nonneg ht.le _)
    _ = _ := by ring




theorem suHomogeneous_base_extension
    {p : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O K : Set (EuclideanSpace ℝ (Fin p))}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (A : EuclideanSpace ℝ (Fin p) × E → F)
    (N : EuclideanSpace ℝ (Fin p) × (ℝ × E) → F)
    {degree : ℝ} (hdegree : -2 ≤ degree)
    (hA : ContDiffOn ℝ 1 A (O ×ˢ Set.univ))
    (hN : ∀ x ∈ O, ∀ t : ℝ, ∀ v : E,
      0 ≤ t → t ^ 2 + ‖v‖ ^ 2 = 1 → ContDiffAt ℝ 1 N (x, t, v))
    (hscale : ∀ x ∈ O, ∀ t : ℝ, 0 < t → ∀ v : E,
      A (x, v) = t ^ degree • N (x, t, t • v)) :
    ∃ (G : EuclideanSpace ℝ (Fin p) × E → F) (C : ℝ),
      ContDiff ℝ 1 G ∧ 0 < C ∧
      (∀ z, ‖fderiv ℝ G z‖ ≤ C * (1 + ‖z‖ ^ 2)) ∧
      ∀ x ∈ K, ∀ v : E, G =ᶠ[𝓝 (x, v)] A := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχO⟩ :=
    Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hK hO hKO
  let G : EuclideanSpace ℝ (Fin p) × E → F := fun z => χ z.1 • A z
  let T : EuclideanSpace ℝ (Fin p) × (ℝ × E) → F := fun z => χ z.1 • N z
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z.1 ∈ O
    · exact (((hχ.of_le (by simp)).contDiffAt).comp z contDiffAt_fst).smul
        (hA.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
    · have hzt : z.1 ∉ tsupport χ := fun ht => hz (hχO ht)
      have he : G =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [continuousAt_fst.preimage_mem_nhds
          ((isClosed_tsupport χ).isOpen_compl.mem_nhds hzt)] with y hy
        simp only [G, image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  obtain ⟨C, hC, hbound⟩ := suNormalizedCoefficient_derivative_bound hχc.isCompact T (by
    rintro ⟨x, t, v⟩ ⟨hx, ht, hv⟩
    exact (((hχ.of_le (by simp)).contDiffAt).comp _ contDiffAt_fst).smul
      (hN x (hχO hx) t v ht hv))
  refine ⟨G, C, hG, hC, ?_, ?_⟩
  · rintro ⟨x, v⟩
    by_cases hx : x ∈ tsupport χ
    · obtain ⟨t, ht, hu, ht1⟩ := suGradientParameters_normalize v
      have he : G =ᶠ[𝓝 (x, v)]
          fun z => t ^ degree • T (z.1, t, t • z.2) := by
        filter_upwards [continuousAt_fst.preimage_mem_nhds (hO.mem_nhds (hχO hx))] with z hz
        dsimp only [G, T]
        rw [hscale z.1 hz t ht z.2, smul_smul, smul_smul, mul_comm]
      have hT : DifferentiableAt ℝ T (x, t, t • v) :=
        (((hχ.of_le (by simp)).contDiffAt.comp _ contDiffAt_fst).smul
          (hN x (hχO hx) t (t • v) ht.le hu)).differentiableAt (by norm_num)
      have hb := (suNormalizedCoefficient_full_bound T x v ht ht1 degree hT
        (hbound x hx t (t • v) ht.le hu)).2
      have hnorm : t ^ (-2 : ℝ) = 1 + ‖v‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hu
        rw [Real.rpow_neg ht.le, Real.rpow_two]
        field_simp
        nlinarith [hu]
      have htbound : t ^ degree ≤ 1 + ‖v‖ ^ 2 := by
        rw [← hnorm]
        exact Real.rpow_le_rpow_of_exponent_ge ht ht1 hdegree
      have hv : ‖v‖ ≤ ‖(x, v)‖ := le_max_right _ _
      rw [he.fderiv_eq]
      exact hb.trans ((mul_le_mul_of_nonneg_left htbound hC.le).trans
        (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg v]) hC.le))
    · have he : G =ᶠ[𝓝 (x, v)] fun _ => 0 := by
        filter_upwards [continuousAt_fst.preimage_mem_nhds
          ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)] with z hz
        simp only [G, image_eq_zero_of_notMem_tsupport hz, zero_smul]
      rw [he.fderiv_eq, fderiv_fun_const, Pi.zero_apply, norm_zero]
      positivity
  · intro x hx v
    filter_upwards [continuousAt_fst.preimage_mem_nhds
      (Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hx))] with z hz
    simp only [G, hχone z.1 (Metric.thickening_subset_cthickening δ K hz), one_smul]





theorem suAlphaFlux_supported_extension
    {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {O K : Set (EuclideanSpace ℝ (Fin p))}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (B : EuclideanSpace ℝ (Fin p) → E →L[ℝ] E →L[ℝ] ℝ)
    (c a : EuclideanSpace ℝ (Fin p) → ℝ) {alpha : ℝ} (ha : alpha ≤ 3 / 2)
    (hB : ContDiffOn ℝ 1 B O) (hc : ContDiffOn ℝ 1 c O) (haa : ContDiffOn ℝ 1 a O)
    (hcpos : ∀ x ∈ O, 0 < c x) (hBpos : ∀ x ∈ O, ∀ v ≠ 0, 0 < B x v v) :
    ∃ (G : EuclideanSpace ℝ (Fin p) × E → E →L[ℝ] ℝ) (C : ℝ),
      ContDiff ℝ 1 G ∧ 0 < C ∧
      (∀ z, ‖fderiv ℝ G z‖ ≤ C * (1 + ‖z‖ ^ 2)) ∧
      ∀ x ∈ K, ∀ v : E,
        G =ᶠ[𝓝 (x, v)] fun z => a z.1 • suAlphaFlux (B z.1) (c z.1) alpha z.2 := by
  let A : EuclideanSpace ℝ (Fin p) × E → E →L[ℝ] ℝ :=
    fun z => a z.1 • suAlphaFlux (B z.1) (c z.1) alpha z.2
  let N : EuclideanSpace ℝ (Fin p) × (ℝ × E) → E →L[ℝ] ℝ :=
    fun z => a z.1 • suAlphaFlux (B z.1) (z.2.1 ^ 2 * c z.1) alpha z.2.2
  have hBnonneg (x : EuclideanSpace ℝ (Fin p)) (hx : x ∈ O) (v : E) : 0 ≤ B x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hBpos x hx v hv).le
  have hNs (x : EuclideanSpace ℝ (Fin p)) (hx : x ∈ O) (t : ℝ) (v : E)
      (hp : 0 < t ^ 2 * c x + B x v v) : ContDiffAt ℝ 1 N (x, t, v) :=
    ((haa.contDiffAt (hO.mem_nhds hx)).comp _ contDiffAt_fst).smul
      (suAlphaFlux_normalized_contDiffAt B c alpha
        (hB.contDiffAt (hO.mem_nhds hx)) (hc.contDiffAt (hO.mem_nhds hx)) hp)
  apply suHomogeneous_base_extension hO hK hKO A N (by linarith : -2 ≤ 1 - 2 * alpha)
  · intro z hz
    have hp : 0 < (1 : ℝ) ^ 2 * c z.1 + B z.1 z.2 z.2 := by
      simpa only [one_pow, one_mul] using add_pos_of_pos_of_nonneg
        (hcpos z.1 hz.1) (hBnonneg z.1 hz.1 z.2)
    have hd := (hNs z.1 hz.1 1 z.2 hp).comp z
      (show ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin p) × E => (y.1, (1 : ℝ), y.2)) z by
        fun_prop)
    change ContDiffAt ℝ 1
      (fun y => a y.1 • suAlphaFlux (B y.1) ((1 : ℝ) ^ 2 * c y.1) alpha y.2) z at hd
    simpa only [A, one_pow, one_mul] using hd.contDiffWithinAt
  · intro x hx t v _ hu
    apply hNs x hx t v
    by_cases hv : v = 0
    · have ht2 : t ^ 2 = 1 := by simpa [hv] using hu
      simpa [hv, ht2] using hcpos x hx
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (hcpos x hx).le)
        (hBpos x hx v hv)
  · intro x hx t ht v
    dsimp only [A, N]
    rw [suAlphaFlux_gradient_scaling (B x) (hBnonneg x hx) (hcpos x hx) ht alpha v]
    simp only [smul_smul, mul_comm]

end PoincareConjecture.M60

end
