import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Period.Slab
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Measure
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Noncollapse
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

/-!
# Volume of a cylindrical quotient with a nonzero translation

The quotient is covered by one slab. Metric-preserving projection and the
exact product volume formula bound its total volume by the factor volume
times the translation length, including arbitrary transverse screw motions.

Reference: Morgan--Tian, Proposition 9.83, p. 236.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.AncientCylinderPeriod

variable {n : ℕ} {N U M : Type*}
  [TopologicalSpace N] [TopologicalSpace U] [TopologicalSpace M]
  [MeasurableSpace N] [BorelSpace N] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace M] [BorelSpace M] [T3Space N] [T3Space U] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) U] [IsManifold (𝓡 (n + 1)) ∞ U]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  [SecondCountableTopology N]

/-- A nonzero cylindrical deck translation bounds the base's total volume
by the volume of one product slab. No order condition is imposed on the
transverse action. -/
theorem calibratedVolume_univ_le_of_translation
    (h : RiemannianMetric n N) (G : RiemannianMetric (n + 1) U)
    (g : RiemannianMetric (n + 1) M)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ U)
    (he : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      G.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
          h.inner z.1 v.1 w.1 + v.2 * w.2)
    {p : U → M} (hp : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ p)
    (hsurj : Function.Surjective p)
    (hinner : ∀ (x : U) (v w : TangentSpace (𝓡 (n + 1)) x),
      G.inner x v w = g.inner (p x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) p x v)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) p x w))
    (d : Equiv.Perm (N × ℝ)) (l : ℝ) (hl : l ≠ 0)
    (hd : ∀ z, (d z).2 = z.2 + l) (hdeck : ∀ z, p (e (d z)) = p (e z)) :
    calibratedMetricVolume g univ ≤ h.volumeMeasure univ * ENNReal.ofReal |l| := by
  let S : Set (N × ℝ) := univ ×ˢ Icc 0 |l|
  have hslab : (p ∘ e) '' S = univ :=
    image_slab_eq_univ_of_nonzero_translation (p ∘ e)
      (hsurj.comp e.surjective) d l hl hd hdeck
  change (fun z => p (e z)) '' S = univ at hslab
  have hv := calibratedMetricVolume_image_le_of_metric_pullback G g hp hinner (e '' S)
  rw [image_image, hslab, calibratedMetricVolume_eq_volumeMeasure g,
    calibratedMetricVolume_eq_volumeMeasure G] at hv
  have hmeasure := h.measurePreserving_productIsometry G e he
  have hprod : G.volumeMeasure (e '' S) = h.volumeMeasure univ * ENNReal.ofReal |l| := by
    have hi : Function.Injective e := e.injective
    rw [← hmeasure.measure_preimage_emb e.toHomeomorph.measurableEmbedding,
      hi.preimage_image]
    simp only [S, Measure.prod_prod, Real.volume_Icc, sub_zero]
  rw [hprod] at hv
  simpa only [calibratedMetricVolume_eq_volumeMeasure] using hv

end PoincareMT.AncientCylinderPeriod
