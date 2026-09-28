import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "FiberBilin" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

structure SmallMetricPerturbation (g₀ : RiemannianMetric n M) where
  tensor : ∀ x : M, FiberBilin x
  symm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    tensor x v w = tensor x w v
  small : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    |tensor x v v| ≤ (1 / 2 : ℝ) * g₀.inner x v v
  smooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x (tensor x))

namespace SmallMetricPerturbation

variable {g₀ : RiemannianMetric n M} (P : SmallMetricPerturbation g₀)

theorem lower_bound (x : M) (v : TangentSpace (𝓡 n) x) :
    (1 / 2 : ℝ) * g₀.inner x v v ≤ g₀.inner x v v + P.tensor x v v := by
  have h := neg_le_of_abs_le (P.small x v)
  linarith

theorem positive (x : M) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) :
    0 < g₀.inner x v v + P.tensor x v v := by
  exact (mul_pos (by norm_num) (g₀.pos x v hv)).trans_le (P.lower_bound x v)

noncomputable def metric : RiemannianMetric n M where
  inner x := g₀.inner x + P.tensor x
  symm x v w := by
    simp only [add_apply]
    rw [g₀.symm]
    exact congrArg (fun z => g₀.inner x w v + z) (P.symm x v w)
  pos x v hv := P.positive x v hv
  isVonNBounded x := by
    let c : ℝ := 1 / 2
    let L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
      (Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x)
    refine ((g₀.isVonNBounded x).image L).subset ?_
    intro v hv
    refine ⟨Real.sqrt c • v, ?_, ?_⟩
    · change g₀.inner x (Real.sqrt c • v) (Real.sqrt c • v) < 1
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : 0 ≤ c)]
      exact (P.lower_bound x v).trans_lt hv
    · change (Real.sqrt c)⁻¹ • (Real.sqrt c • v) = v
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : 0 < c)),
        one_smul]
  contMDiff := g₀.contMDiff.add_section P.smooth

@[simp] theorem metric_inner (x : M) (v w : TangentSpace (𝓡 n) x) :
    P.metric.inner x v w = g₀.inner x v w + P.tensor x v w := rfl

theorem metric_lower_bound (x : M) (v : TangentSpace (𝓡 n) x) :
    (1 / 2 : ℝ) * g₀.inner x v v ≤ P.metric.inner x v v := by
  exact P.lower_bound x v

theorem metric_positive (x : M) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) :
    0 < P.metric.inner x v v := by
  exact P.positive x v hv

end SmallMetricPerturbation

noncomputable def SmallMetricPerturbation.zero (g₀ : RiemannianMetric n M) :
    SmallMetricPerturbation g₀ where
  tensor := fun _ => 0
  symm := by simp
  small := by
    intro x v
    simp only [zero_apply, abs_zero]
    by_cases hv : v = 0
    · simp [hv]
    · exact (mul_pos (by norm_num) (g₀.pos x v hv)).le
  smooth := by
    change ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (Bundle.zeroSection (E →L[ℝ] E →L[ℝ] ℝ) (fun x : M => FiberBilin x))
    exact Bundle.contMDiff_zeroSection ℝ _

@[simp] theorem SmallMetricPerturbation.zero_metric
    (g₀ : RiemannianMetric n M) :
    (SmallMetricPerturbation.zero g₀).metric = g₀ := by
  have hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (SmallMetricPerturbation.zero g₀).metric.inner x v w = g₀.inner x v w := by
    intro x v w
    change g₀.inner x v w + (0 : FiberBilin x) v w = g₀.inner x v w
    simp
  cases h₁ : (SmallMetricPerturbation.zero g₀).metric
  cases h₂ : g₀
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [h₁, h₂] using hinner x v w

structure SmallMetricPath (g₀ : RiemannianMetric n M) (J : Set ℝ) where
  tensor : ℝ → ∀ x : M, FiberBilin x
  symm : ∀ (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x),
    tensor t x v w = tensor t x w v
  small : ∀ (t : ℝ) (x : M) (v : TangentSpace (𝓡 n) x),
    |tensor t x v v| ≤ (1 / 2 : ℝ) * g₀.inner x v v
  slice_smooth : ∀ t : ℝ,
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x (tensor t x))
  joint_smooth : RiemannianMetric.IsSmoothFamilyOn
      (fun t => SmallMetricPerturbation.metric
        ({ tensor := tensor t
           symm := symm t
           small := small t
           smooth := slice_smooth t } : SmallMetricPerturbation g₀)) J
  initial_zero : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    tensor 0 x v w = 0

namespace SmallMetricPath

variable {g₀ : RiemannianMetric n M} {J : Set ℝ}
  (P : SmallMetricPath g₀ J)

noncomputable def slice (t : ℝ) : SmallMetricPerturbation g₀ where
  tensor := P.tensor t
  symm := P.symm t
  small := P.small t
  smooth := P.slice_smooth t

noncomputable def metric (t : ℝ) : RiemannianMetric n M := (P.slice t).metric

@[simp] theorem metric_inner (t : ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (P.metric t).inner x v w = g₀.inner x v w + P.tensor t x v w := rfl

theorem metric_initial : P.metric 0 = g₀ := by
  have hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (P.metric 0).inner x v w = g₀.inner x v w := by
    intro x v w
    rw [P.metric_inner, P.initial_zero]
    simp
  cases h₁ : P.metric 0
  cases h₂ : g₀
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simpa only [h₁, h₂] using hinner x v w

theorem metric_isSmoothFamilyOn :
    RiemannianMetric.IsSmoothFamilyOn P.metric J := by
  change RiemannianMetric.IsSmoothFamilyOn
    (fun t => (P.slice t).metric) J
  exact P.joint_smooth

theorem metric_lower_bound (t : ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    (1 / 2 : ℝ) * g₀.inner x v v ≤ (P.metric t).inner x v v := by
  exact (P.slice t).metric_lower_bound x v

end SmallMetricPath

end PoincareConjecture
