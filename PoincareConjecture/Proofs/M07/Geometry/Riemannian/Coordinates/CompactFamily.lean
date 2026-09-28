import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem exists_uniform_bilinear_family_lower_bound
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {K : Set X} (hK : IsCompact K)
    (hB : ContinuousOn B K) (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcompact := hK.prod (isCompact_sphere (0 : E) 1)
  have hcoeff : ContinuousOn (fun z : X × E => B z.1) (K ×ˢ Metric.sphere 0 1) :=
    hB.comp continuousOn_fst (fun z hz => hz.1)
  have henergy := (hcoeff.clm_apply continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' henergy (fun z hz =>
    hpos z.1 hz.1 z.2 (by
      have hn : ‖z.2‖ = 1 := by simpa [Metric.mem_sphere] using hz.2
      intro hzero
      simp [hzero] at hn))
  refine ⟨c, hc, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
  have h := hbound (x, (‖v‖⁻¹ : ℝ) • v) ⟨hx, by simpa [Metric.mem_sphere] using hnorm⟩
  calc
    c * ‖v‖ ^ 2 ≤ B x ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
    _ = B x v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp [norm_ne_zero_iff.mpr hv]

theorem eventually_bilinear_error_lt_on_unit_sublevels
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Bseq : ℕ → X → E →L[ℝ] E →L[ℝ] ℝ} {B : X → E →L[ℝ] E →L[ℝ] ℝ}
    {K : Set X} (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hconv : TendstoUniformlyOn Bseq B atTop K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v w : E,
      B x v v ≤ 1 → B x w w ≤ 1 → |Bseq k x v w - B x v w| < ε := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_family_lower_bound hK hB hpos
  let R := c⁻¹ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hnorm (x : X) (hx : x ∈ K) (v : E) (hv : B x v v ≤ 1) : ‖v‖ ≤ R := by
    have hs : ‖v‖ ^ 2 ≤ c⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hc]
      nlinarith [hbound x hx v]
    dsimp [R]
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  have htol : 0 < ε / R ^ 2 := div_pos hε (sq_pos_of_pos hR)
  filter_upwards [(Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hconv (ε / R ^ 2) htol]
    with k hk x hx v w hv hw
  have hd : ‖Bseq k x - B x‖ < ε / R ^ 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hk x hx
  have hb := (Bseq k x - B x).le_opNorm₂ v w
  have hn : ‖v‖ * ‖w‖ ≤ R ^ 2 := by
    simpa only [pow_two] using mul_le_mul (hnorm x hx v hv) (hnorm x hx w hw)
      (norm_nonneg _) hR.le
  calc
    |Bseq k x v w - B x v w| ≤ ‖Bseq k x - B x‖ * (‖v‖ * ‖w‖) := by
      simpa only [sub_apply, Real.norm_eq_abs, mul_assoc] using hb
    _ ≤ ‖Bseq k x - B x‖ * R ^ 2 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ < ε := (lt_div_iff₀ (sq_pos_of_pos hR)).mp hd

end PoincareConjecture
