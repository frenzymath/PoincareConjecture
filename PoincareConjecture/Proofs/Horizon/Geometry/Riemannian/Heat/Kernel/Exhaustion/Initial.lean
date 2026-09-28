import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Properties
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Monotone








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}

private theorem tendsto_integral_of_dominating_dirichletKernel
    {Ω : Set M} {K : ℝ → M → M → ℝ}
    (hK : Dirichlet.IsDirichletHeatKernel D Ω K)
    {x : M} (hx : x ∈ Ω) {H : ℝ → M → ℝ}
    (hHi : ∀ t, 0 < t → Integrable (H t) g.volumeMeasure)
    (hHm : ∀ t, 0 < t → (∫ y, H t y ∂g.volumeMeasure) ≤ 1)
    (hdom : ∀ t, 0 < t → ∀ y, K t x y ≤ H t y)
    {φ : M → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ y, ‖φ y‖ ≤ B) :
    Tendsto (fun t => ∫ y, H t y * φ y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (φ x)) := by
  have hB0 : 0 ≤ B := (norm_nonneg (φ x)).trans (hB x)
  have hplus_bound (y : M) : ‖B + φ y‖ ≤ 2 * B := by
    calc
      _ ≤ ‖B‖ + ‖φ y‖ := norm_add_le _ _
      _ ≤ 2 * B := by rw [Real.norm_of_nonneg hB0]; linarith [hB y]
  have hminus_bound (y : M) : ‖B - φ y‖ ≤ 2 * B := by
    calc
      _ ≤ ‖B‖ + ‖φ y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by rw [Real.norm_of_nonneg hB0]; linarith [hB y]
  have hHiφ (t : ℝ) (ht : 0 < t) :
      Integrable (fun y => H t y * φ y) g.volumeMeasure :=
    (hHi t ht).mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hB)
  have hbounds (t : ℝ) (ht : 0 < t) :
      (∫ y, K t x y * (B + φ y) ∂g.volumeMeasure) - B ≤
          (∫ y, H t y * φ y ∂g.volumeMeasure) ∧
        (∫ y, H t y * φ y ∂g.volumeMeasure) ≤
          B - (∫ y, K t x y * (B - φ y) ∂g.volumeMeasure) := by
    have hKi := hK.integrable_ambient ht x
    have hHi' := hHi t ht
    have hplus : (∫ y, K t x y * (B + φ y) ∂g.volumeMeasure) ≤
        B + (∫ y, H t y * φ y ∂g.volumeMeasure) := by
      calc
        _ ≤ ∫ y, H t y * (B + φ y) ∂g.volumeMeasure := by
          apply integral_mono
            (hKi.mul_bdd (continuous_const.add hφ).aestronglyMeasurable
              (ae_of_all _ hplus_bound))
            (hHi'.mul_bdd (continuous_const.add hφ).aestronglyMeasurable
              (ae_of_all _ hplus_bound))
          intro y
          have hy : -B ≤ φ y := (abs_le.mp (hB y)).1
          exact mul_le_mul_of_nonneg_right (hdom t ht y)
            (by change 0 ≤ B + φ y; linarith)
        _ = (∫ y, H t y ∂g.volumeMeasure) * B +
            (∫ y, H t y * φ y ∂g.volumeMeasure) := by
          simp_rw [mul_add]
          rw [integral_add (hHi'.mul_const B) (hHiφ t ht), integral_mul_const]
        _ ≤ _ := by nlinarith [hHm t ht]
    have hminus : (∫ y, K t x y * (B - φ y) ∂g.volumeMeasure) ≤
        B - (∫ y, H t y * φ y ∂g.volumeMeasure) := by
      calc
        _ ≤ ∫ y, H t y * (B - φ y) ∂g.volumeMeasure := by
          apply integral_mono
            (hKi.mul_bdd (continuous_const.sub hφ).aestronglyMeasurable
              (ae_of_all _ hminus_bound))
            (hHi'.mul_bdd (continuous_const.sub hφ).aestronglyMeasurable
              (ae_of_all _ hminus_bound))
          intro y
          have hy : φ y ≤ B := (abs_le.mp (hB y)).2
          exact mul_le_mul_of_nonneg_right (hdom t ht y) (sub_nonneg.mpr hy)
        _ = (∫ y, H t y ∂g.volumeMeasure) * B -
            (∫ y, H t y * φ y ∂g.volumeMeasure) := by
          simp_rw [mul_sub]
          rw [integral_sub (hHi'.mul_const B) (hHiφ t ht), integral_mul_const]
        _ ≤ _ := by nlinarith [hHm t ht]
    constructor <;> linarith
  have hplus := hK.tendsto_integral_ambient_initial (φ := fun y => B + φ y)
    (continuous_const.add hφ).continuousOn hx
  have hminus := hK.tendsto_integral_ambient_initial (φ := fun y => B - φ y)
    (continuous_const.sub hφ).continuousOn hx
  have hlower : Tendsto
      (fun t => (∫ y, K t x y * (B + φ y) ∂g.volumeMeasure) - B)
      (𝓝[>] 0) (𝓝 (φ x)) := by
    simpa using hplus.sub_const B
  have hupper : Tendsto
      (fun t => B - (∫ y, K t x y * (B - φ y) ∂g.volumeMeasure))
      (𝓝[>] 0) (𝓝 (φ x)) := by
    simpa using hminus.const_sub B
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hbounds t ht).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hbounds t ht).2



theorem tendsto_integral_iSup_dirichletHeatKernel_initial_of_bounded
    {Ω : ℕ → Set M} {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hcover : (⋃ j, Ω j) = univ)
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    (hbdd : ∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y)))
    {φ : M → ℝ} (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, ‖φ y‖ ≤ B) (x : M) :
    Tendsto (fun t => ∫ y, (⨆ j, K j t x y) * φ y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (φ x)) := by
  have hx : x ∈ ⋃ j, Ω j := by rw [hcover]; trivial
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
  have hmass (t : ℝ) (ht : 0 < t) :=
    g.integrable_iSup_of_monotone_of_integral_le
      (fun j => (hK j).integrable_ambient ht x)
      (fun j y => (hK j).nonneg t ht x y) (hmono t ht x) (hbdd t ht x)
      (fun j => (hK j).integral_ambient_le_one ht x)
  exact tendsto_integral_of_dominating_dirichletKernel (hK j) hxj
    (fun t ht => (hmass t ht).1) (fun t ht => (hmass t ht).2)
    (fun t ht y => le_ciSup (hbdd t ht x y) j) hφ hB



theorem tendsto_integral_iSup_dirichletHeatKernel_initial
    {Ω : ℕ → Set M} {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hcover : (⋃ j, Ω j) = univ)
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    (hbdd : ∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y)))
    {φ : M → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (x : M) :
    Tendsto (fun t => ∫ y, (⨆ j, K j t x y) * φ y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (φ x)) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hφ
  exact tendsto_integral_iSup_dirichletHeatKernel_initial_of_bounded
    hK hcover hmono hbdd hφ hB x

end PoincareConjecture.LeviCivitaData
