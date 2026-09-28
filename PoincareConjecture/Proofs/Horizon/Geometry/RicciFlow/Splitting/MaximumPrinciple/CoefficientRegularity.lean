import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartOperator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem pullback_coefficients_smooth_within
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) {t : ℝ} (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ univ) (t, x) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [RiemannianMetric.constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2))
      (J ×ˢ univ) (t, x) :=
    contDiffWithinAt_fst.contMDiffWithinAt.prodMk contDiffWithinAt_snd.contMDiffWithinAt
  convert! (hc.comp (t, x) hid (fun _ hp => hp)).contDiffWithinAt using 1

theorem contDiffOn_chartMetric {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => chartMetric (g z.1) p z.2)
      (J ×ˢ (extChartAt (𝓡 n) p).target) := by
  intro z hz
  apply (pullback_coefficients_smooth_within hg
    ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz.2)) hz.1).mono
  exact prod_mono_right (subset_univ _)

private theorem spatialFDeriv_within
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => fderiv ℝ (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  have hd := (hf.fderivWithin (hJ.prod hU.uniqueDiffOn) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  apply hd.congr
  intro z hz
  have hcomp := ((hf z hz).differentiableWithinAt (by simp)).hasFDerivWithinAt.comp z.2
    (((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)).hasFDerivWithinAt)
    (show MapsTo (fun x : V => (z.1, x)) U (J ×ˢ U) from fun _ hx => ⟨hz.1, hx⟩)
  exact (hcomp.hasFDerivAt (hU.mem_nhds hz.2)).fderiv

theorem contDiffOn_chartMetric_inverse {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (chartMetric (g z.1) p z.2).inverse)
      (J ×ˢ (extChartAt (𝓡 n) p).target) := by
  intro z hz
  exact (((g z.1).isInvertible_chartCoefficients p hz.2).contDiffAt_map_inverse).comp_contDiffWithinAt
    z (contDiffOn_chartMetric hg p z hz)

theorem contDiffOn_chartDrift {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : UniqueDiffOn ℝ J) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => chartDrift (g z.1) p z.2)
      (J ×ˢ (extChartAt (𝓡 n) p).target) := by
  have hi := contDiffOn_chartMetric_inverse hg p
  have hd := spatialFDeriv_within (contDiffOn_chartMetric hg p) hJ
    (isOpen_extChartAt_target p)
  have hf : ContDiff ℝ ∞ (fun A :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun A :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).contDiff
  let E := EuclideanSpace ℝ (Fin n)
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  change ContDiffOn ℝ ∞ (fun z : ℝ × E => ∑ i,
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (chartMetric (g z.1) p z.2).inverse).comp
      ((2⁻¹ : ℝ) • (fderiv ℝ (chartMetric (g z.1) p) z.2 +
        (flipL.comp (fderiv ℝ (chartMetric (g z.1) p) z.2)).flip -
          flipL.comp (fderiv ℝ (chartMetric (g z.1) p) z.2).flip)))
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((chartMetric (g z.1) p z.2).inverse (EuclideanSpace.proj i))) _
  fun_prop

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
