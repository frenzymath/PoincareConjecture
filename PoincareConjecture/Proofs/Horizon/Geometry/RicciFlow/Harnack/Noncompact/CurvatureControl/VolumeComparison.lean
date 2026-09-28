import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.CompactVolume
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem volumeMeasure_lower_bound_of_integral_scalarCurvature_le
    (F : RicciFlow n M J) {a b P : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hD : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    {S K : Set M} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K)
    (hP : ∀ t ∈ Ioo a b,
      (∫ y in S, (F.connection t).scalarCurvature y ∂(F.metric t).volumeMeasure) ≤ P) :
    ((F.metric a).volumeMeasure S).toReal - P * (b - a) ≤
      ((F.metric b).volumeMeasure S).toReal := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => ((F.metric s).volumeMeasure S).toReal)
        (-(∫ y in S, (F.connection t).scalarCurvature y
          ∂(F.metric t).volumeMeasure)) t :=
    F.hasDerivAt_volumeMeasure_of_subset (hJ ht) (hD t ht) hS hK hSK
  have hcont : ContinuousOn (fun s => ((F.metric s).volumeMeasure S).toReal) (Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => ((F.metric s).volumeMeasure S).toReal)
      (interior (Icc a b)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ interior (Icc a b),
      -P ≤ deriv (fun s => ((F.metric s).volumeMeasure S).toReal) t := by
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact neg_le_neg (hP t (by simpa only [interior_Icc] using ht))
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff hbound
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  linarith

theorem antitoneOn_volumeMeasure_of_integral_scalarCurvature_nonneg
    (F : RicciFlow n M J) {a b : ℝ}
    (hJ : Icc a b ⊆ interior J)
    (hD : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    {S K : Set M} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K)
    (hR : ∀ t ∈ Ioo a b, 0 ≤
      ∫ y in S, (F.connection t).scalarCurvature y ∂(F.metric t).volumeMeasure) :
    AntitoneOn (fun t => ((F.metric t).volumeMeasure S).toReal) (Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => ((F.metric s).volumeMeasure S).toReal)
        (-(∫ y in S, (F.connection t).scalarCurvature y
          ∂(F.metric t).volumeMeasure)) t :=
    F.hasDerivAt_volumeMeasure_of_subset (hJ ht) (hD t ht) hS hK hSK
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  exact neg_nonpos.mpr (hR t (by simpa only [interior_Icc] using ht))

theorem antitoneOn_volumeMeasure_of_scalarCurvature_nonneg
    (F : RicciFlow n M J) {a b : ℝ}
    (hJ : Icc a b ⊆ interior J)
    (hD : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    {S K : Set M} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K)
    (hR : ∀ t ∈ Icc a b, ∀ x ∈ S, 0 ≤ (F.connection t).scalarCurvature x) :
    AntitoneOn (fun t => ((F.metric t).volumeMeasure S).toReal) (Icc a b) := by
  apply F.antitoneOn_volumeMeasure_of_integral_scalarCurvature_nonneg hJ hD hS hK hSK
  intro t ht
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hR t (Ioo_subset_Icc_self ht) x hx

end PoincareConjecture.RicciFlow
