import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Global







set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)


theorem integral_mul_comp_coarea
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ U) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x, w (f x) * h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
      ∫ c : ℝ, w c * ∫ z, h (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c := by
  have hsupport : tsupport (fun x => w (f x) * h x) ⊆ U :=
    tsupport_mul_subset_right.trans hs
  have hi := g.integral_coarea hf U hreg ((hw.comp hf.continuous).mul hh)
    hc.mul_left hsupport
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    change w (f x) * h x * g.tangentNorm x (g.gradient f x) = 0
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero,
      zero_mul])] at hi
  have hleft : (∫ x, w (f x) * h x * g.tangentNorm x (g.gradient f x)
      ∂g.volumeMeasure) =
      ∫ x, (w ∘ f * h) x * g.tangentNorm x (g.gradient f x)
        ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    rfl
  rw [hleft, hi]
  apply integral_congr_ae
  filter_upwards [] with c
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : f (openLevelIncl f U c z) = c := z.2
  change w (f (openLevelIncl f U c z)) * h (openLevelIncl f U c z) = _
  rw [hz]

end PoincareConjecture.RiemannianMetric
