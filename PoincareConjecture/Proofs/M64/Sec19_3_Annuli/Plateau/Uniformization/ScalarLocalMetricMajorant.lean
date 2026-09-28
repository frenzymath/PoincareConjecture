import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarC1MetricMajorant












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Form" => Plane →L[ℝ] Plane →L[ℝ] ℝ

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]






theorem scalarLocalC1_exists_smooth_metric_majorant
    (g : RiemannianMetric n M) (f : Plane → M)
    {K U : Set Plane} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ q : RiemannianMetric 2 Plane, ∀ x ∈ K, ∀ v : Plane,
      g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v) +
          delta * ‖v‖ ^ 2 ≤ q.inner x v v ∧
      q.inner x v v ≤
        g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v) +
          2 * delta * ‖v‖ ^ 2 := by
  obtain ⟨V, hV, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨chi, hchi, hchirange, hchisupp, hchione⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓡 2) (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  let A : Plane → Form := fun x => M60.metricPullbackForm (n := 2) g f x
  let B : Plane → Form := fun x => chi x • A x
  have hB : Continuous B := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ tsupport chi
    · have hxU : x ∈ U := hVU (by simpa only [tsupport, hchisupp] using hx)
      exact hchi.continuous.continuousAt.smul
        (scalarC1_pullback_continuousAt g (hf.contMDiffAt (hU.mem_nhds hxU)))
    · apply (continuousAt_const (y := (0 : Form))).congr
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change chi y = 0 at hy
      ext v w
      change (0 : ℝ) = chi y * A y v w
      rw [hy, zero_mul]
  have hnonneg (x v : Plane) : 0 ≤ B x v v := by
    have ha : 0 ≤ A x v v := by
      change 0 ≤ g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v)
      by_cases hv : mfderiv (𝓡 2) (𝓡 n) f x v = 0
      · simp [hv]
      · exact (g.pos _ _ hv).le
    exact mul_nonneg (hchirange (mem_range_self x)).1 ha
  obtain ⟨q, hq⟩ := scalarContinuousForm_exists_smooth_metric_majorant B hB hnonneg delta hdelta
  refine ⟨q, ?_⟩
  intro x hx v
  have heq : B x = A x := by simp only [B, (hchione x).mp hx, one_smul]
  simpa only [heq, A, M60.metricPullbackForm_apply] using! hq x v

end PoincareConjecture.M64Uniformization
