import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative
import PoincareConjecture.Proofs.M03.Existence.CompactSupportLpNative

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace PoincareConjecture.EuclideanRellichNative

open EuclideanTranslationNative EuclideanMollificationNative CompactSupportLpNative

variable {n : ℕ} {ε : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def restrictedKernel (K : Set E) (hε : 0 < ε) : C(K, ScalarL2 n) :=
  ⟨fun x => mollifierKernel hε x, (continuous_mollifierKernel hε).comp continuous_subtype_val⟩

def compactMollifier {K : Set E} (hK : IsCompact K) (hε : 0 < ε) :
    ScalarL2 n →L[ℝ] ScalarL2 n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (extensionOperator hK).comp
    (CompactKernelNative.kernelOperator (restrictedKernel K hε))

theorem isCompactOperator_compactMollifier {K : Set E} (hK : IsCompact K) (hε : 0 < ε) :
    IsCompactOperator (compactMollifier hK hε) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompactOperator_extendedKernel hK (restrictedKernel K hε)

theorem compactMollifier_ae_eq {K : Set E} (hK : IsCompact K) (hε : 0 < ε)
    (F : ScalarL2 n) :
    compactMollifier hK hε F =ᵐ[volume] K.indicator (mollify hε F) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  change extensionLp hK (CompactKernelNative.kernelFunction (restrictedKernel K hε) F)
    =ᵐ[volume] _
  filter_upwards [extensionLp_ae_eq hK
    (CompactKernelNative.kernelFunction (restrictedKernel K hε) F)] with x hx
  rw [hx]
  by_cases hxK : x ∈ K
  · rw [extension_of_mem K _ hxK, indicator_of_mem hxK]
    rfl
  · rw [extension_of_notMem K _ hxK, indicator_of_notMem hxK]

theorem norm_compactMollifier_error_sq_le {K : Set E} (hK : IsCompact K) (hε : 0 < ε)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume)
    (hsupport : ∀ x ∉ K, f x = 0) :
    ‖compactMollifier hK hε (hfL2.toLp f) - hfL2.toLp f‖ ^ 2 ≤
      ε ^ 2 * gradientEnergy f := by
  calc
    _ = ∫ x, ((compactMollifier hK hε (hfL2.toLp f) - hfL2.toLp f) x) ^ 2 :=
      scalarLp_norm_sq _
    _ ≤ ∫ x, (mollify hε (hfL2.toLp f) x - f x) ^ 2 := by
      apply integral_mono_ae (Lp.memLp _).integrable_sq
        (integrable_mollify_error_sq hε hf hfL2 hcoord)
      filter_upwards [Lp.coeFn_sub (compactMollifier hK hε (hfL2.toLp f)) (hfL2.toLp f),
        compactMollifier_ae_eq hK hε (hfL2.toLp f), hfL2.coeFn_toLp] with x hsub hA hfx
      rw [hsub, Pi.sub_apply, hA, hfx]
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hsupport x hx, sub_self, zero_pow (by norm_num)]
        exact sq_nonneg _
    _ ≤ _ := integral_mollify_error_sq_le hε hf hfL2 hcoord

theorem norm_compactMollifier_error_le {K : Set E} (hK : IsCompact K) (hε : 0 < ε)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hfL2 : MemLp f 2 volume)
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume)
    (hsupport : ∀ x ∉ K, f x = 0) {D : ℝ} (hD : 0 ≤ D)
    (henergy : gradientEnergy f ≤ D ^ 2) :
    ‖compactMollifier hK hε (hfL2.toLp f) - hfL2.toLp f‖ ≤ ε * D := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε.le hD)).mp
  calc
    _ ≤ ε ^ 2 * gradientEnergy f :=
      norm_compactMollifier_error_sq_le hK hε hf hfL2 hcoord hsupport
    _ ≤ ε ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left henergy (sq_nonneg ε)
    _ = _ := (mul_pow ε D 2).symm

theorem totallyBounded_of_compact_approximation {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {S : Set H} {R : ℝ}
    (hR : ∀ u ∈ S, ‖u‖ ≤ R)
    (happrox : ∀ δ > 0, ∃ A : H →L[ℝ] H,
      IsCompactOperator A ∧ ∀ u ∈ S, ‖A u - u‖ < δ) :
    TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro δ hδ
  obtain ⟨A, hA, herr⟩ := happrox (δ / 2) (half_pos hδ)
  have hc : IsCompact (closure (A '' Metric.closedBall (0 : H) R)) :=
    hA.isCompact_closure_image_closedBall (f := A.toLinearMap) R
  obtain ⟨C, hCfin, hC⟩ := Metric.totallyBounded_iff.mp hc.totallyBounded
    (δ / 2) (half_pos hδ)
  refine ⟨C, hCfin, ?_⟩
  intro u hu
  have hAu : A u ∈ closure (A '' Metric.closedBall (0 : H) R) :=
    subset_closure ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hR u hu, rfl⟩
  obtain ⟨c, hAc⟩ := mem_iUnion.mp (hC hAu)
  obtain ⟨hcC, hAc⟩ := mem_iUnion.mp hAc
  apply mem_iUnion.mpr
  refine ⟨c, mem_iUnion.mpr ⟨hcC, ?_⟩⟩
  rw [Metric.mem_ball] at hAc ⊢
  have hua : dist u (A u) < δ / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact herr u hu
  exact (dist_triangle u (A u) c).trans_lt (by linarith)

theorem totallyBounded_supported_C1 {K : Set E} (hK : IsCompact K)
    {S : Set (ScalarL2 n)} {R D : ℝ} (hD : 0 ≤ D)
    (hR : ∀ u ∈ S, ‖u‖ ≤ R)
    (hS : ∀ u ∈ S, ∃ f : E → ℝ, ∃ hf : ContDiff ℝ 1 f,
      ∃ hfL2 : MemLp f 2 volume,
      (∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) ∧
      (∀ x ∉ K, f x = 0) ∧ u = hfL2.toLp f ∧ gradientEnergy f ≤ D ^ 2) :
    TotallyBounded S := by
  apply totallyBounded_of_compact_approximation hR
  intro δ hδ
  let ε : ℝ := δ / (D + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  refine ⟨compactMollifier hK hε, isCompactOperator_compactMollifier hK hε, ?_⟩
  intro u hu
  obtain ⟨f, hf, hfL2, hcoord, hsupp, rfl, henergy⟩ := hS u hu
  apply (norm_compactMollifier_error_le hK hε hf hfL2 hcoord hsupp hD henergy).trans_lt
  have heq : ε * (D + 1) = δ := div_mul_cancel₀ δ (by linarith : D + 1 ≠ 0)
  nlinarith

theorem isCompact_closure_supported_C1 {K : Set E} (hK : IsCompact K)
    {S : Set (ScalarL2 n)} {R D : ℝ} (hD : 0 ≤ D)
    (hR : ∀ u ∈ S, ‖u‖ ≤ R)
    (hS : ∀ u ∈ S, ∃ f : E → ℝ, ∃ hf : ContDiff ℝ 1 f,
      ∃ hfL2 : MemLp f 2 volume,
      (∀ i : Fin n, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) ∧
      (∀ x ∉ K, f x = 0) ∧ u = hfL2.toLp f ∧ gradientEnergy f ≤ D ^ 2) :
    IsCompact (closure S) :=
  (totallyBounded_supported_C1 hK hD hR hS).closure.isCompact_of_isClosed isClosed_closure

section GraphClosure

variable {V H : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H]

theorem value_mem_closure_bounded_image (p : V → H) (hp : Continuous p)
    {S : Set V} {x : V} (hx : x ∈ closure S) {R : ℝ} (hxR : ‖x‖ ≤ R) :
    p x ∈ closure (p '' (S ∩ Metric.ball 0 (R + 1))) := by
  have hxb : x ∈ Metric.ball 0 (R + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hxi : x ∈ closure (S ∩ Metric.ball 0 (R + 1)) :=
    Metric.isOpen_ball.closure_inter ⟨hx, hxb⟩
  exact image_closure_subset_closure_image hp ⟨x, hxi, rfl⟩

theorem totallyBounded_bounded_graph_closure (p : V → H) (hp : Continuous p)
    {S : Set V} {R : ℝ}
    (hS : TotallyBounded (p '' (S ∩ Metric.ball 0 (R + 1)))) :
    TotallyBounded (p '' (closure S ∩ Metric.closedBall 0 R)) := by
  apply hS.closure.subset
  rintro _ ⟨x, ⟨hx, hxR⟩, rfl⟩
  exact value_mem_closure_bounded_image p hp hx
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxR)

theorem isCompact_closure_bounded_graph_image [CompleteSpace H]
    (p : V → H) (hp : Continuous p) {S : Set V} {R : ℝ}
    (hS : TotallyBounded (p '' (S ∩ Metric.ball 0 (R + 1)))) :
    IsCompact (closure (p '' (closure S ∩ Metric.closedBall 0 R))) :=
  (totallyBounded_bounded_graph_closure p hp hS).closure.isCompact_of_isClosed isClosed_closure

end GraphClosure

end PoincareConjecture.EuclideanRellichNative
