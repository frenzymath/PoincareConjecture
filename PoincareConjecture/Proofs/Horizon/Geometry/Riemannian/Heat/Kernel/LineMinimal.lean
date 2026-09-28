import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineComparison
import PoincareConjecture.Proofs.Horizon.Analysis.Heat.RealKernel
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineArclength

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal Manifold
open Poincare.Analysis.Heat

namespace PoincareConjecture.RiemannianMetric

theorem realHeatKernel_le_of_nonnegative_heat_solution
    {u : ℝ → ℝ → ℝ} {y : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0))
    (hspace : ∀ t, 0 < t → ContDiff ℝ 2 (fun x => u x t))
    (hheat : ∀ x t, 0 < t → HasDerivAt (u x)
      (deriv (deriv (fun z => u z t)) x) t)
    (hnonneg : ∀ x t, 0 < t → 0 ≤ u x t)
    (htrace : ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun t => ∫ z, φ z * u z t) (𝓝[>] 0) (𝓝 (φ y)))
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    realHeatKernel t (y - x) ≤ u x t := by
  let χ : ContDiffBump y := default
  have hχone : χ y = 1 := χ.eventuallyEq_one.self_of_nhds
  have hcompare (τ : ℝ) (hτ : 0 < τ) :
      (∫ z, realHeatKernel t (z - x) * χ z * u z τ) ≤ u x (t + τ) := by
    let f : ℝ → ℝ := fun z => χ z * u z τ
    have hf : ContDiff ℝ 2 f := χ.contDiff.mul (hspace τ hτ)
    have hfc : HasCompactSupport f := χ.hasCompactSupport.mul_right
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by norm_num)
    obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hf.continuous
    have hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 (p.2 + τ)) (univ ×ˢ Icc 0 t) := by
      apply hcont.comp (f := fun p : ℝ × ℝ => (p.1, p.2 + τ)) (by fun_prop)
      intro p hp
      have hp0 : 0 ≤ p.2 := hp.2.1
      exact ⟨trivial, add_pos_of_nonneg_of_pos hp0 hτ⟩
    have h := gaussianAverage_le_nonnegative_supersolution hL
      (hf.differentiable (by norm_num)) hB
      (u := fun z s => u z (s + τ))
      (ut := fun z s => deriv (deriv (fun w => u w (s + τ))) z) hc
      (fun s hs => hspace (s + τ) (by linarith [hs.1]))
      (fun z s hs => by
        have hd := (hheat z (s + τ) (by linarith [hs.1])).comp s
          ((hasDerivAt_id s).add_const τ)
        simpa only [mul_one, Function.comp_def, id_eq] using
          hd.hasDerivWithinAt (s := Icc 0 t))
      (fun _ _ _ => le_rfl)
      (fun z s hs => hnonneg z (s + τ) (by linarith [hs.1]))
      (fun z => by
        dsimp only [f]
        simp only [zero_add]
        exact mul_le_of_le_one_left (hnonneg z τ hτ) χ.le_one) x t ⟨ht.le, le_rfl⟩
    rw [gaussianAverage_eq_integral_realHeatKernel hf.continuous ht] at h
    simpa only [f, mul_assoc] using h
  have hk : Continuous (fun z => realHeatKernel t (z - x)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_realHeatKernel_space ht (z - x)).continuousAt.comp
      (f := fun w : ℝ => w - x) (by fun_prop)
  have hlim := htrace (fun z => realHeatKernel t (z - x) * χ z)
    (hk.mul χ.continuous) χ.hasCompactSupport.mul_left
  rw [hχone, mul_one] at hlim
  have hright : Tendsto (fun τ => u x (t + τ)) (𝓝[>] 0) (𝓝 (u x t)) := by
    have hc := (hheat x t ht).continuousAt
    have hd : Tendsto (fun τ : ℝ => t + τ) (𝓝[>] 0) (𝓝 t) := by
      simpa using ((show Continuous (fun τ : ℝ => t + τ) by fun_prop).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
    exact hc.tendsto.comp hd
  apply le_of_tendsto_of_tendsto hlim hright
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact hcompare τ hτ

theorem realHeatKernel_coordinate_le_of_nonnegative_heat_solution
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
    (g : RiemannianMetric 1 M) (D : LeviCivitaData g) (e : M ≃ ℝ)
    (he : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ e)
    (hi : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e.symm)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 1) x),
      g.inner x v w = mvfderiv (𝓡 1) e x v * mvfderiv (𝓡 1) e x w)
    {u : M → ℝ → ℝ} {y : M}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0))
    (hspace : ∀ t, 0 < t → ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hheat : ∀ x t, 0 < t → HasDerivAt (u x) (D.laplacian (fun z => u z t) x) t)
    (hnonneg : ∀ x t, 0 < t → 0 ≤ u x t)
    (htrace : ∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure) (𝓝[>] 0) (𝓝 (φ y)))
    {t : ℝ} (ht : 0 < t) (x : M) :
    realHeatKernel t (e y - e x) ≤ u x t := by
  let eh : M ≃ₜ ℝ := { e with continuous_toFun := he.continuous, continuous_invFun := hi.continuous }
  have hed := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp))
    (hi.of_le (by simp)) hmetric
  have hμ := g.measurePreserving_volumeMeasure_real e hed
  let v : ℝ → ℝ → ℝ := fun z s => u (e.symm z) s
  have hvspace (s : ℝ) (hs : 0 < s) : ContDiff ℝ ∞ (fun z => v z s) :=
    contMDiff_iff_contDiff.mp ((hspace s hs).comp hi)
  have hlap (s : ℝ) (hs : 0 < s) (z : ℝ) :
      D.laplacian (fun p => u p s) (e.symm z) = deriv (deriv (fun w => v w s)) z := by
    have hid : (fun p => u p s) = (fun w => v w s) ∘ e := by
      funext p
      simp [v]
    rw [hid, D.laplacian_comp he (hvspace s hs),
      D.laplacian_eq_zero_of_unit_gradient he
        (fun p => D.inner_gradient_eq_one_of_metric_coordinate (hmetric p)),
      D.inner_gradient_eq_one_of_metric_coordinate (hmetric _)]
    simp
  have hc : ContinuousOn (Function.uncurry v) (univ ×ˢ Ioi 0) := by
    apply hcont.comp (f := fun p : ℝ × ℝ => (e.symm p.1, p.2))
      ((hi.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
    exact fun p hp => ⟨trivial, hp.2⟩
  have h := realHeatKernel_le_of_nonnegative_heat_solution
    (u := v) (y := e y) hc
    (fun s hs => (contDiff_infty.mp (hvspace s hs)) 2)
    (fun z s hs => by rw [← hlap s hs z]; exact hheat (e.symm z) s hs)
    (fun z s hs => hnonneg (e.symm z) s hs) (fun φ hφ hφc => ?_) ht (e x)
  · simpa only [v, Equiv.symm_apply_apply] using h
  · have hp := htrace (φ ∘ e) (hφ.comp he.continuous) (hφc.comp_homeomorph eh)
    have heq (s : ℝ) : (∫ z, φ z * v z s) =
        ∫ p, (φ ∘ e) p * u p s ∂g.volumeMeasure := by
      have hh := hμ.integral_comp eh.measurableEmbedding (fun z => φ z * v z s)
      simpa only [Function.comp_apply, v, Equiv.symm_apply_apply] using hh.symm
    simpa only [heq, Function.comp_apply] using hp

theorem exists_minimal_smooth_conservativeHeatKernel_dim_one
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric 1 M) (hc : MetricComplete g) (D : LeviCivitaData g) :
    ∃ H : M → M → ℝ → ℝ,
      (∀ x y t, 0 < t → 0 < H x y t) ∧
      ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 1)).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : (ℝ × M) × M => H p.1.2 p.2 p.1.1) ((Ioi 0 ×ˢ univ) ×ˢ univ) ∧
      (∀ x y t, 0 < t → HasDerivAt (fun s => H x y s)
        (D.laplacian (fun z => H z y t) x) t) ∧
      (∀ x y t, H x y t = H y x t) ∧
      (∀ x t, 0 < t → ∫ y, H x y t ∂g.volumeMeasure = 1) ∧
      (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ → ∀ x,
        Tendsto (fun t => ∫ y, H x y t * φ y ∂g.volumeMeasure)
          (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ x t, 0 < t → Integrable
        (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure) ∧
      (∀ x t, 0 < t → t ≤ 1 →
        ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure ≤ Real.sqrt 2) ∧
      Tendsto (fun t => ⨆ x,
        ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) (𝓝[>] 0) (𝓝 0) ∧
      (∀ (u : M → ℝ → ℝ) (y : M),
        ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0) →
        (∀ t, 0 < t → ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun x => u x t)) →
        (∀ x t, 0 < t → HasDerivAt (u x) (D.laplacian (fun z => u z t) x) t) →
        (∀ x t, 0 < t → 0 ≤ u x t) →
        (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
          Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure) (𝓝[>] 0) (𝓝 (φ y))) →
        ∀ x t, 0 < t → H x y t ≤ u x t) := by
  obtain ⟨e, he, hi, hmetric⟩ := g.exists_metric_line_coordinate hc
  have hed := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp))
    (hi.of_le (by simp)) hmetric
  refine ⟨fun x y t => realHeatKernel t (e y - e x), ?_,
    LeviCivitaData.contMDiffOn_realHeatKernel_coordinate he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x y t ht => transported_realHeatKernel_pos g e hed ht x y
  · exact fun x y t ht => D.hasDerivAt_realHeatKernel_of_metric_coordinate he hmetric y ht x
  · intro x y t
    simp only [realHeatKernel]
    congr 2
    congr 2
    ring
  · exact fun x t ht => transported_realHeatKernel_mass_one g e hed ht x
  · exact fun φ hφ hφc x => tendsto_transported_realHeatKernel_initial g e hed hφ hφc x
  · exact fun x t ht => transported_realHeatKernel_first_moment_integrable g e hed ht x
  · exact fun x t ht ht1 => transported_realHeatKernel_first_moment_bound g e hed ht ht1 x
  · exact tendsto_transported_realHeatKernel_first_moment g e hed
  · intro u y hcont hspace hheat hnonneg htrace x t ht
    exact realHeatKernel_coordinate_le_of_nonnegative_heat_solution g D e he hi hmetric
      hcont hspace hheat hnonneg htrace ht x

end PoincareConjecture.RiemannianMetric
