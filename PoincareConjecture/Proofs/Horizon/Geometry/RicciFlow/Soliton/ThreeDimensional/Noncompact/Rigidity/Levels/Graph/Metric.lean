import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.AreaConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n m : ℕ} {N L M : Type*}
  [TopologicalSpace N] [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) L]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 m) ∞ L] [IsManifold (𝓡 m) ∞ M]



theorem exists_metric_on_embedded_height_graph
    (g : RiemannianMetric m M) (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 m⟯ L)
    (E : L → M) {U : Set L} (hU : IsOpen U)
    (hE : ContMDiffOn (𝓡 m) (𝓡 m) ∞ E U)
    (hEi : ∀ x ∈ U, Injective (mfderiv (𝓡 m) (𝓡 m) E x))
    (u : N → ℝ) (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hmem : ∀ y, e (y, u y) ∈ U) :
    ∃ h : RiemannianMetric n N,
      ∀ (y : N) (v w : TangentSpace (𝓡 n) y),
        h.inner y v w = g.inner (E (e (y, u y)))
          (mfderiv (𝓡 n) (𝓡 m) (fun z => E (e (z, u z))) y v)
          (mfderiv (𝓡 n) (𝓡 m) (fun z => E (e (z, u z))) y w) := by
  let j : N → N × ℝ := fun y => (y, u y)
  have hj : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ j := contMDiff_id.prodMk hu
  have hψ : ContMDiff (𝓡 n) (𝓡 m) ∞ (E ∘ e ∘ j) := fun y =>
    (hE.contMDiffAt (hU.mem_nhds (hmem y))).comp y ((e.contMDiff (j y)).comp y (hj y))
  have hψi (y : N) : Injective (mfderiv (𝓡 n) (𝓡 m) (E ∘ e ∘ j) y) := by
    rw [mfderiv_comp y
      ((hE.contMDiffAt (hU.mem_nhds (hmem y))).mdifferentiableAt (by simp))
      (((e.contMDiff (j y)).comp y (hj y)).mdifferentiableAt (by simp)),
      mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) _)
        (hj.mdifferentiable (by simp) _)]
    apply (hEi _ (hmem y)).comp
    apply ((e.mfderivToContinuousLinearEquiv (by simp) (j y)).injective).comp
    have hjd := mfderiv_prodMk mdifferentiableAt_id (hu.mdifferentiable (by simp) y)
    simp only [id_eq] at hjd
    change Injective (mfderiv (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ℝ)) (fun z => (z, u z)) y)
    rw [hjd, mfderiv_id]
    intro v w heq
    exact congrArg Prod.fst heq
  exact ⟨Induced.pullbackMetric g (E ∘ e ∘ j) hψ hψi, fun _ _ _ => rfl⟩



theorem product_metric_height_graph_inner
    (h : RiemannianMetric n N) (g : RiemannianMetric m L)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 m⟯ L)
    (hproduct : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 m) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 m) e z w) = h.inner z.1 v.1 w.1 + v.2 * w.2)
    {u : N → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (y : N) (v : TangentSpace (𝓡 n) y) :
    g.inner (e (y, u y))
      (mfderiv (𝓡 n) (𝓡 m) (fun z => e (z, u z)) y v)
      (mfderiv (𝓡 n) (𝓡 m) (fun z => e (z, u z)) y v) =
        h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2 := by
  have hj := mdifferentiableAt_id.prodMk (hu.mdifferentiable (by simp) y)
  have hcomp := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (y, u y)) hj
  change mfderiv (𝓡 n) (𝓡 m) (fun z => e (z, u z)) y = _ at hcomp
  rw [hcomp]
  change g.inner _
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 m) e (y, u y) _)
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 m) e (y, u y) _) = _
  rw [hproduct, mfderiv_prodMk mdifferentiableAt_id (hu.mdifferentiable (by simp) y), mfderiv_id]
  change h.inner y v v + mvfderiv (𝓡 n) u y v * mvfderiv (𝓡 n) u y v = _
  ring



theorem height_graph_relative_metric_error
    (h : RiemannianMetric n N) (gk : RiemannianMetric n N)
    {u : N → ℝ} {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hambient : ∀ (y : N) (v : TangentSpace (𝓡 n) y),
      |gk.inner y v v - (h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2)| ≤
        ε * (h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2))
    (hu : ∀ (y : N) (v : TangentSpace (𝓡 n) y),
      |mvfderiv (𝓡 n) u y v| ≤ η * h.tangentNorm y v)
    (y : N) (v : TangentSpace (𝓡 n) y) :
    |gk.inner y v v - h.inner y v v| ≤ (ε * (1 + η ^ 2) + η ^ 2) * h.inner y v v := by
  have hn : 0 ≤ h.inner y v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (h.pos y v hz).le
  have hsq : (mvfderiv (𝓡 n) u y v) ^ 2 ≤ η ^ 2 * h.inner y v v := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hη (Real.sqrt_nonneg _))).mpr (hu y v)
    simpa only [sq_abs, mul_pow, tangentNorm, Real.sq_sqrt hn] using hh
  calc
    _ = |(gk.inner y v v - (h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2)) +
        (mvfderiv (𝓡 n) u y v) ^ 2| := by congr 1; ring
    _ ≤ |gk.inner y v v - (h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2)| +
        |(mvfderiv (𝓡 n) u y v) ^ 2| := abs_add_le _ _
    _ ≤ ε * (h.inner y v v + (mvfderiv (𝓡 n) u y v) ^ 2) +
        (mvfderiv (𝓡 n) u y v) ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg (mvfderiv (𝓡 n) u y v))]
      exact add_le_add (hambient y v) le_rfl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsq hε]

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

variable {N : Type*} [TopologicalSpace N] [T3Space N]
  [MeasurableSpace N] [BorelSpace N] [CompactSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]



theorem tendsto_area_of_height_graph_metric_error
    (h : RiemannianMetric 2 N) (gseq : ℕ → RiemannianMetric 2 N)
    (u : ℕ → N → ℝ)
    (hambient : ∀ ε > 0, ∀ᶠ k in atTop, ∀ (y : N) (v : TangentSpace (𝓡 2) y),
      |(gseq k).inner y v v - (h.inner y v v + (mvfderiv (𝓡 2) (u k) y v) ^ 2)| ≤
        ε * (h.inner y v v + (mvfderiv (𝓡 2) (u k) y v) ^ 2))
    (hdu : ∀ η > 0, ∀ᶠ k in atTop, ∀ (y : N) (v : TangentSpace (𝓡 2) y),
      |mvfderiv (𝓡 2) (u k) y v| ≤ η * h.tangentNorm y v) :
    Tendsto (fun k => (gseq k).volumeMeasure.real univ) atTop
      (𝓝 (h.volumeMeasure.real univ)) := by
  apply tendsto_area_of_uniform_relative_quadraticForm_error gseq h
  intro δ hδ
  let ρ := min 1 (δ / 3)
  have hρ : 0 < ρ := lt_min zero_lt_one (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρδ : 3 * ρ ≤ δ := by
    have h := min_le_right 1 (δ / 3)
    dsimp only [ρ]
    linarith
  have hconstant : ρ * (1 + ρ ^ 2) + ρ ^ 2 ≤ δ := by
    have hs : ρ ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hρ.le
    nlinarith
  filter_upwards [hambient ρ hρ, hdu ρ hρ] with k hk hu
  intro y v
  have hn : 0 ≤ h.inner y v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (h.pos y v hz).le
  exact (h.height_graph_relative_metric_error (gseq k) hρ.le hρ.le hk hu y v).trans
    (mul_le_mul_of_nonneg_right hconstant hn)

end PoincareConjecture.RiemannianMetric
