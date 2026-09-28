import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Topology.Order.Compact








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem exists_uniform_bilinear_lower_bound
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {K : Set E} (hK : IsCompact K)
    (hB : ContinuousOn B K) (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcompact := hK.prod (isCompact_sphere (0 : E) 1)
  have hcoeff : ContinuousOn (fun z : E × E => B z.1) (K ×ˢ Metric.sphere 0 1) :=
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



theorem isCompact_bilinear_energy_sublevel
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {K : Set E} (hK : IsCompact K)
    (hB : ContinuousOn B K) (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (R : ℝ) :
    IsCompact {z : E × E | z.1 ∈ K ∧ B z.1 z.2 z.2 ≤ R} := by
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound hK hB hpos
  let r := max (R / c) 0 + 1
  have hsub : {z : E × E | z.1 ∈ K ∧ B z.1 z.2 z.2 ≤ R} ⊆
      K ×ˢ Metric.closedBall 0 r := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hsquare : ‖z.2‖ ^ 2 ≤ R / c :=
      (le_div_iff₀ hc).mpr (by nlinarith [hbound z.1 hz.1 z.2, hz.2])
    have hmax := le_max_left (R / c) 0
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp only [r]
    nlinarith [sq_nonneg (‖z.2‖ - 1 / 2)]
  have hcoeff : ContinuousOn (fun z : E × E => B z.1) (K ×ˢ Metric.closedBall 0 r) :=
    hB.comp continuousOn_fst (fun z hz => hz.1)
  have henergy := (hcoeff.clm_apply continuousOn_snd).clm_apply continuousOn_snd
  have heq : {z : E × E | z.1 ∈ K ∧ B z.1 z.2 z.2 ≤ R} =
      (K ×ˢ Metric.closedBall 0 r) ∩ {z | B z.1 z.2 z.2 ≤ R} := by
    ext z
    exact ⟨fun hz => ⟨hsub hz, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [heq]
  have hcompact := hK.prod (isCompact_closedBall (0 : E) r)
  exact hcompact.of_isClosed_subset
    (henergy.preimage_isClosed_of_isClosed hcompact.isClosed isClosed_Iic) inter_subset_left

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

open scoped Manifold ContDiff



theorem isCompact_chart_energy_sublevel
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hsub : K ⊆ (extChartAt (𝓡 n) p).target) (R : ℝ) :
    IsCompact {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      z.1 ∈ K ∧ g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.1 z.2 z.2 ≤ R} := by
  apply isCompact_bilinear_energy_sublevel hK
    ((g.contDiffOn_chartCoefficients p).continuousOn.mono hsub)
  intro x hx v hv
  have hAv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x v ≠ 0 := by
    intro hzero
    obtain ⟨e, he⟩ := g.isInvertible_chartCoefficients p (hsub hx)
    apply hv
    apply e.injective
    change (e : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v = e 0
    rw [map_zero, he]
    ext w
    change g.inner ((extChartAt (𝓡 n) p).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm x w) = 0
    rw [hzero]
    simp +instances only [map_zero, zero_apply]
  exact g.pos _ _ hAv

end PoincareConjecture.RiemannianMetric
