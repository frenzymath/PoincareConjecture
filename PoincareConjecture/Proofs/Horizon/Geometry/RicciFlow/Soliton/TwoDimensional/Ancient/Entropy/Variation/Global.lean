import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Variation.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Partition








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] {J : Set ℝ}



theorem hasDerivAt_integral_volumeMeasure_surface
    (F : RicciFlow 2 M J) {t : ℝ} (ht : t ∈ interior J)
    {u : ℝ → M → ℝ}
    (hu : ∀ s ∈ interior J, ∀ y : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (s, y)) :
    HasDerivAt (fun s => ∫ x, u s x ∂(F.metric s).volumeMeasure)
      (∫ x, deriv (fun s => u s x) t -
        (F.connection t).scalarCurvature x * u t x ∂(F.metric t).volumeMeasure) t := by
  classical
  have hus (r : ℝ) (hr : r ∈ interior J) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (u r) :=
    fun x => (hu r hr x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hud (x : M) : DifferentiableAt ℝ (fun r => u r x) t := by
    have h := (hu t ht x).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
    exact h.contDiffAt.differentiableAt (by simp)
  have hdt : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => deriv (fun r => u r x) t) :=
    fun x => (Poincare.Manifold.contMDiffAt_deriv_time (hu t ht x)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  let V : M → ℝ := fun x => deriv (fun r => u r x) t -
    (F.connection t).scalarCurvature x * u t x
  have hV : Continuous V := hdt.continuous.sub
    ((F.connection t).continuous_scalarCurvature.mul (hus t ht).continuous)
  obtain ⟨s, w, hw, hwc, hws, hsum⟩ :=
    PoincareConjecture.exists_finite_chart_decomposition (n := 2)
      (contMDiff_const : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 : ℝ)))
      (HasCompactSupport.of_compactSpace _)
  let φ : M → ℝ → M → ℝ := fun i r x => w i x * u r x
  have hφ (i : M) (r : ℝ) (hr : r ∈ interior J) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => φ i p.1 p.2) (r, x) :=
    ((hw i x).comp (r, x) contMDiffAt_snd).mul (hu r hr x)
  have hφd (i x : M) : deriv (fun r => φ i r x) t -
      (F.connection t).scalarCurvature x * φ i t x = w i x * V x := by
    dsimp only [φ]
    rw [deriv_const_mul _ (hud x)]
    dsimp [V]
    ring
  have hlocal (i : M) :
      HasDerivAt (fun r => ∫ x, φ i r x ∂(F.metric r).volumeMeasure)
        (∫ x, w i x * V x ∂(F.metric t).volumeMeasure) t := by
    let e := (chartAt (EuclideanSpace ℝ (Fin 2)) i).symm
    let K := e.symm '' tsupport (w i)
    have hK : IsCompact K := (hwc i).isCompact.image_of_continuousOn
      (e.symm.continuousOn.mono (hws i))
    have hKe : K ⊆ e.source := by
      rintro x ⟨y, hy, rfl⟩
      exact e.map_target (hws i hy)
    have heK : e '' K = tsupport (w i) :=
      e.image_symm_image_of_subset_target (hws i)
    have hd := F.hasDerivAt_integral_volumeMeasure_image_surface ht (hφ i)
      e contMDiffOn_chart_symm contMDiffOn_chart hK.measurableSet hK Subset.rfl hKe
    rw [heK] at hd
    have hfun : (fun r => ∫ x, φ i r x ∂(F.metric r).volumeMeasure) =ᶠ[𝓝 t]
        (fun r => ∫ x in tsupport (w i), φ i r x ∂(F.metric r).volumeMeasure) := by
      filter_upwards [] with r
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by simp only [φ, image_eq_zero_of_notMem_tsupport hx, zero_mul])).symm
    apply (hd.congr_of_eventuallyEq hfun).congr_deriv
    simp_rw [hφd]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
  have hi (i : M) (r : ℝ) (hr : r ∈ interior J) :
      Integrable (φ i r) (F.metric r).volumeMeasure :=
    ((hw i).continuous.mul (hus r hr).continuous).integrable_of_hasCompactSupport
      (hwc i).mul_right
  have hiV (i : M) : Integrable (fun x => w i x * V x) (F.metric t).volumeMeasure :=
    ((hw i).continuous.mul hV).integrable_of_hasCompactSupport (hwc i).mul_right
  have hsumint (r : ℝ) (hr : r ∈ interior J) :
      (∫ x, u r x ∂(F.metric r).volumeMeasure) =
        ∑ i ∈ s, ∫ x, φ i r x ∂(F.metric r).volumeMeasure := by
    rw [← integral_finsetSum s (fun i _ => hi i r hr)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [φ, ← Finset.sum_mul, hsum x, one_mul]
  have hder : HasDerivAt (fun r => ∑ i ∈ s, ∫ x, φ i r x ∂(F.metric r).volumeMeasure)
      (∑ i ∈ s, ∫ x, w i x * V x ∂(F.metric t).volumeMeasure) t :=
    HasDerivAt.fun_sum (fun i _ => hlocal i)
  have hevent : (fun r => ∫ x, u r x ∂(F.metric r).volumeMeasure) =ᶠ[𝓝 t]
      (fun r => ∑ i ∈ s, ∫ x, φ i r x ∂(F.metric r).volumeMeasure) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with r hr
    exact hsumint r hr
  apply (hder.congr_of_eventuallyEq hevent).congr_deriv
  rw [← integral_finsetSum s (fun i _ => hiV i)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.sum_mul, hsum x, one_mul]

end PoincareConjecture.RicciFlow
