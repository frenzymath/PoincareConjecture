import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.CompactComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Volume.LocalVolume
import Mathlib.Topology.Compactness.LocallyCompact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]

theorem calibratedVolume_le_of_tangentNorm_le (g h : RiemannianMetric n M)
    {V S : Set M} (hV : IsOpen V) (hS : MeasurableSet S) (hSV : S ⊆ V)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ c * g.tangentNorm x v) :
    calibratedMetricVolume h S ≤ ENNReal.ofReal c ^ n * calibratedMetricVolume g S := by
  have hb : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm ((OpenPartialHomeomorph.refl M) x)
        (mfderiv (𝓡 n) (𝓡 n) (OpenPartialHomeomorph.refl M) x v) ≤
          c * g.tangentNorm x v := by
    intro x hx v
    change h.tangentNorm x (mfderiv (𝓡 n) (𝓡 n) id x v) ≤ _
    rw [mfderiv_id]
    exact hbound x hx v
  have hvol := g.volumeMeasure_image_le_of_tangentNorm_le h (OpenPartialHomeomorph.refl M)
      hV (subset_univ V) contMDiff_id.contMDiffOn hc hb hS hSV
  change h.volumeMeasure (id '' S) ≤ ENNReal.ofReal c ^ n * g.volumeMeasure S at hvol
  simpa only [image_id, Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure]
    using hvol

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_terminal_calibratedVolume_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ t in 𝓝[<] T, ∀ S : Set (H.regularRegion P04), MeasurableSet S → S ⊆ A →
      calibratedMetricVolume (H.terminalMetric P04) S ≤
        ENNReal.ofReal c ^ 3 * calibratedMetricVolume ((H.terminalFlow P04).metric t) S ∧
      calibratedMetricVolume ((H.terminalFlow P04).metric t) S ≤
        ENNReal.ofReal c ^ 3 * calibratedMetricVolume (H.terminalMetric P04) S := by
  let _ : LocallyCompactSpace (H.regularRegion P04) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  obtain ⟨B, hB, hAB⟩ := exists_compact_superset hA
  filter_upwards [H.eventually_terminal_tangentNorm_comparison P04 hB hc] with t ht S hS hSA
  have hcpos := zero_lt_one.trans hc
  exact ⟨SingularRegularLimit.calibratedVolume_le_of_tangentNorm_le
      ((H.terminalFlow P04).metric t) (H.terminalMetric P04)
      isOpen_interior hS (hSA.trans hAB) hcpos
      (fun x hx v => (ht x (interior_subset hx) v).1),
    SingularRegularLimit.calibratedVolume_le_of_tangentNorm_le
      (H.terminalMetric P04) ((H.terminalFlow P04).metric t)
      isOpen_interior hS (hSA.trans hAB) hcpos
      (fun x hx v => (ht x (interior_subset hx) v).2)⟩


theorem terminalFlow_reference_calibratedVolume
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    {S : Set (H.regularRegion P04)} (hS : MeasurableSet S) :
    calibratedMetricVolume (F.metric t)
        ((fun x : H.regularRegion P04 => H.reference.forward t ht x) '' S) =
      calibratedMetricVolume ((H.terminalFlow P04).metric t) S := by
  let f : H.regularRegion P04 → (F.slice t).carrier :=
    fun x => H.reference.forward t ht x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (H.reference.forward_smooth t ht).comp contMDiff_subtype_val
  have hinj : Function.Injective f :=
    (H.reference.left_inverse t ht).injective.comp Subtype.val_injective
  have hinner (x : H.regularRegion P04) (v w : TangentSpace (𝓡 3) x) :
      ((H.terminalFlow P04).metric t).inner x v w =
        (F.metric t).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    have hd := mfderiv_comp x
      ((H.reference.forward_smooth t ht).mdifferentiable (by simp) (x : M))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x)
    change mfderiv (𝓡 3) (𝓡 3) f x = _ at hd
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply,
      Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal,
      ContinuousLinearMap.id_apply]
    change (H.terminalMetricFamily P04 t).inner x v w = _
    rw [H.terminalMetricFamily_inner_of_ne P04 ht.2.ne]
    exact (H.reference.metric_pullback t ht x v w).symm
  simpa only [Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure] using
    ((H.terminalFlow P04).metric t).volumeMeasure_image_eq_of_injOn_metric_pullback
      (F.metric t) hf hinner isOpen_univ hinj.injOn hS (subset_univ S)

end PoincareConjecture.SingularTimeAssumptions
