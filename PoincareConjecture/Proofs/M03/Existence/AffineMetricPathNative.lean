import PoincareConjecture.Proofs.M03.Existence.MetricPerturbationNative
import PoincareConjecture.Proofs.M03.Existence.ConjugatingFlowNative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 1200000
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

def affineTimeCoeff (T t : ℝ) : ℝ :=
  if t ∈ Set.Ico (0 : ℝ) T then t else 0

theorem affineTimeCoeff_eq (T t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    affineTimeCoeff T t = t := by
  simp [affineTimeCoeff, ht]

theorem affineTimeCoeff_nonneg {T t : ℝ} (hT : 0 < T) :
    0 ≤ affineTimeCoeff T t := by
  by_cases ht : t ∈ Set.Ico (0 : ℝ) T
  · rw [affineTimeCoeff_eq T t ht]
    exact ht.1
  · simp [affineTimeCoeff, ht]

theorem affineTimeCoeff_le {T t : ℝ} (hT : 0 < T) :
    affineTimeCoeff T t ≤ T := by
  by_cases ht : t ∈ Set.Ico (0 : ℝ) T
  · rw [affineTimeCoeff_eq T t ht]
    exact ht.2.le
  · simp [affineTimeCoeff, ht]
    exact hT.le

theorem affineTimeCoeff_zero {T : ℝ} (hT : 0 < T) :
    affineTimeCoeff T 0 = 0 := by
  rw [affineTimeCoeff_eq T 0]
  exact ⟨le_rfl, hT⟩

theorem metric_inner_nonneg (g₀ : RiemannianMetric n M)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    0 ≤ g₀.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g₀.pos x v hv).le

structure AffineMetricPathData (g₀ : RiemannianMetric n M) where
  direction : ∀ x : M, FiberBilin x
  symm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    direction x v w = direction x w v
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  direction_bound : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    |direction x v v| ≤ bound * g₀.inner x v v
  spatial_smooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x (direction x))
  T : ℝ
  hT : 0 < T
  horizon_small : bound * T ≤ (1 / 2 : ℝ)
  slice_smooth : ∀ t : ℝ,
    ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x
          (affineTimeCoeff T t • direction x))
  joint_smooth : RiemannianMetric.IsSmoothFamilyOn
    (fun t : ℝ =>
      SmallMetricPerturbation.metric
        ({ tensor := fun x => affineTimeCoeff T t • direction x
           symm := fun x v w => by
             rw [smul_apply, smul_apply, smul_eq_mul,
               smul_apply, smul_apply, smul_eq_mul, symm]
           small := by
             intro x v
             have hc := affineTimeCoeff_nonneg (T := T) (t := t) hT
             have hcT := affineTimeCoeff_le (T := T) (t := t) hT
             have hA := metric_inner_nonneg g₀ x v
             calc
               |(affineTimeCoeff T t • direction x) v v| =
                   affineTimeCoeff T t * |direction x v v| := by
                 simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
                   abs_mul, abs_of_nonneg hc]
               _ ≤ affineTimeCoeff T t * (bound * g₀.inner x v v) := by
                 exact mul_le_mul_of_nonneg_left
                   (direction_bound x v) hc
               _ = (affineTimeCoeff T t * bound) * g₀.inner x v v := by
                 ring
               _ ≤ (T * bound) * g₀.inner x v v := by
                 exact mul_le_mul_of_nonneg_right
                   (mul_le_mul_of_nonneg_right hcT bound_nonneg) hA
               _ ≤ (1 / 2 : ℝ) * g₀.inner x v v := by
                 exact mul_le_mul_of_nonneg_right
                   (by simpa [mul_comm] using horizon_small) hA
           smooth := slice_smooth t } :
          SmallMetricPerturbation g₀)) (Set.Ico 0 T)

namespace AffineMetricPathData

variable {g₀ : RiemannianMetric n M} (A : AffineMetricPathData g₀)

noncomputable def slice (t : ℝ) : SmallMetricPerturbation g₀ :=
  { tensor := fun x => affineTimeCoeff A.T t • A.direction x
    symm := fun x v w => by
      rw [smul_apply, smul_apply, smul_eq_mul,
        smul_apply, smul_apply, smul_eq_mul, A.symm]
    small := by
      intro x v
      have hc := affineTimeCoeff_nonneg (T := A.T) (t := t) A.hT
      have hcT := affineTimeCoeff_le (T := A.T) (t := t) A.hT
      have hA := metric_inner_nonneg g₀ x v
      calc
        |(affineTimeCoeff A.T t • A.direction x) v v| =
            affineTimeCoeff A.T t * |A.direction x v v| := by
          simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
            abs_mul, abs_of_nonneg hc]
        _ ≤ affineTimeCoeff A.T t * (A.bound * g₀.inner x v v) := by
          exact mul_le_mul_of_nonneg_left (A.direction_bound x v) hc
        _ = (affineTimeCoeff A.T t * A.bound) * g₀.inner x v v := by
          ring
        _ ≤ (A.T * A.bound) * g₀.inner x v v := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcT A.bound_nonneg) hA
        _ ≤ (1 / 2 : ℝ) * g₀.inner x v v := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [mul_comm] using A.horizon_small) hA
    smooth := A.slice_smooth t }

noncomputable def metric (t : ℝ) : RiemannianMetric n M :=
  (A.slice t).metric

theorem metric_inner (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (A.metric t).inner x v w =
      g₀.inner x v w + affineTimeCoeff A.T t * A.direction x v w := by
  change g₀.inner x v w +
      (affineTimeCoeff A.T t • A.direction x) v w = _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem metric_isSmoothFamilyOn :
    RiemannianMetric.IsSmoothFamilyOn A.metric (Set.Ico 0 A.T) := by
  change RiemannianMetric.IsSmoothFamilyOn
    (fun t => SmallMetricPerturbation.metric (A.slice t)) (Set.Ico 0 A.T)
  exact A.joint_smooth

theorem metric_initial : A.metric 0 = g₀ := by
  have hzero : affineTimeCoeff A.T 0 = 0 := affineTimeCoeff_zero A.hT
  have hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (A.metric 0).inner x v w = g₀.inner x v w := by
    intro x v w
    rw [A.metric_inner, hzero]
    simp
  cases h₁ : A.metric 0
  cases h₂ : g₀
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact hinner x v w

theorem metric_affine_on_interval {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) A.T) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (A.metric t).inner x v w =
      g₀.inner x v w + t * A.direction x v w := by
  rw [A.metric_inner, affineTimeCoeff_eq A.T t ht]

theorem metric_intervalIntegral {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) A.T) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (A.metric t).inner x v w = g₀.inner x v w +
      ∫ s in (0 : ℝ)..t, A.direction x v w := by
  rw [A.metric_affine_on_interval ht]
  rw [intervalIntegral.integral_const]
  simp

noncomputable def toSmallMetricPath :
    SmallMetricPath g₀ (Set.Ico (0 : ℝ) A.T) where
  tensor := fun t x => affineTimeCoeff A.T t • A.direction x
  symm := fun t x v w => by
    rw [smul_apply, smul_apply, smul_eq_mul,
      smul_apply, smul_apply, smul_eq_mul, A.symm]
  small := by
    intro t x v
    exact (A.slice t).small x v
  slice_smooth := A.slice_smooth
  joint_smooth := by
    change RiemannianMetric.IsSmoothFamilyOn
      (fun t => SmallMetricPerturbation.metric (A.slice t)) (Set.Ico 0 A.T)
    exact A.joint_smooth
  initial_zero := by
    intro x v w
    simp [affineTimeCoeff_zero A.hT,
      ContinuousLinearMap.smul_apply]

theorem metric_eq_toSmallMetricPath (t : ℝ) :
    (A.toSmallMetricPath.metric t) = A.metric t := by
  have hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (A.toSmallMetricPath.metric t).inner x v w =
        (A.metric t).inner x v w := by
    intro x v w
    change g₀.inner x v w +
        affineTimeCoeff A.T t * A.direction x v w =
      g₀.inner x v w + affineTimeCoeff A.T t * A.direction x v w
    rfl
  cases h₁ : A.toSmallMetricPath.metric t
  cases h₂ : A.metric t
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact hinner x v w

theorem exists_metricFamily_of_affine_source
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (D : ∀ t : ℝ, LeviCivitaData (A.toSmallMetricPath.metric t))
    (hEq : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) A.T → ∀ (x : M)
      (u v : TangentSpace (𝓡 n) x),
      A.direction x u v = -2 * (D t).ricci x u v) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g₀ ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (D' : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D'.ricci x u v) (Set.Ico 0 T) t := by
  apply exists_metricFamily_of_intervalIntegral_source
    (g₀ := g₀) (T := A.T) A.hT A.toSmallMetricPath
    (h := fun _ x u v => A.direction x u v)
    (hcont := by
      intro x u v
      exact continuousOn_const)
    (hint := by
      intro t ht x u v
      exact A.metric_intervalIntegral ht x u v)
    D
  exact hEq

end AffineMetricPathData

end PoincareConjecture
