import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.SpatialRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback

set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

namespace RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem contDiffAt_family_pullback_inner (F : RicciFlow n M J)
    {f : ℝ × EuclideanSpace ℝ (Fin n) → M}
    {p : ℝ × EuclideanSpace ℝ (Fin n)} (hJ : J ∈ 𝓝 p.1)
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f p)
    (v w : ℝ × EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun z => (F.metric z.1).inner (f z)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z v)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z w)) p := by
  have hdom : J ×ˢ (univ : Set M) ∈ 𝓝 (p.1, f p) :=
    prod_mem_nhds hJ (Filter.univ_mem)
  have hfst : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) p :=
    contDiffAt_fst.contMDiffAt
  have hg := (F.smooth.contMDiffAt hdom).comp p (hfst.prodMk hf)
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1

end RicciFlow

namespace FlowCarrier

theorem contDiffAt_coordinateCoefficient_metric {n : ℕ} (C : FlowCarrier n)
    (g : C.metric) (q : C.carrier) (a b : Fin n) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n))
    (hy :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      y ∈ (extChartAt (𝓡 n) q).target) :
    ContDiffAt ℝ ∞ (fun z => C.coordinateCoefficient q
      (fun _ x v w => C.metricInner g x v w) a b (t, z)) y := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
    (extChartAt_target_mem_nhds' hy)
  exact g.contDiffAt_pullback_inner hc
    (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)

theorem coordinateCoefficient_metric_det_ne_zero {n : ℕ} (C : FlowCarrier n)
    (g : C.metric) (q : C.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    (Matrix.of (fun a b : Fin n => C.coordinateCoefficient q
      (fun _ x v w => C.metricInner g x v w) a b p)).det ≠ 0 := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  have hi : (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm p.2).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hp
  exact g.pullback_gram_det_ne_zero ((extChartAt (𝓡 n) q).symm p.2)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm p.2).toLinearMap hi.injective

end FlowCarrier

namespace BasedFlow

theorem contDiffAt_coordinateCoefficient_metric
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n} (F : BasedFlow n T' T C)
    (q : C.carrier) (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ContDiffAt ℝ ∞ (C.coordinateCoefficient q
      (fun t x v w => C.metricInner (F.metricAt t) x v w) a b) p := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let c := extChartAt (𝓡 n) q
  let f : ℝ × EuclideanSpace ℝ (Fin n) → C.carrier := fun z => c.symm z.2
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z.2 ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z := by
    have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
    exact hc.comp z contDiffAt_snd.contMDiffAt
  apply (F.flow.contDiffAt_family_pullback_inner (isOpen_Ioo.mem_nhds ht)
    (hf hp) (0, EuclideanSpace.basisFun (Fin n) ℝ a)
      (0, EuclideanSpace.basisFun (Fin n) ℝ b)).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp)]
    with z hz
  have ha := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))
    (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hb := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))
    (EuclideanSpace.basisFun (Fin n) ℝ b)
  rw [← ha, ← hb]
  rfl

end BasedFlow

namespace SmoothSpacetimeEmbedding

theorem contDiffAt_coordinateCoefficient_pullback
    {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U)
    (q : C.carrier) (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target ∧ (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ContDiffAt ℝ ∞ (C.coordinateCoefficient q (pullbackInnerValue F G e) a b) p := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let c := extChartAt (𝓡 n) q
  let f : ℝ × EuclideanSpace ℝ (Fin n) → D.carrier :=
    fun z => (e.toFun (z.1, c.symm z.2)).2
  have hc {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)}
      (hz : z.1 ∈ Ioo T' T ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z := by
    have hfst : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) z :=
      contDiffAt_fst.contMDiffAt
    have hsnd : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.2) z :=
      contDiffAt_snd.contMDiffAt
    exact ((e.smooth_on.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      ⟨hz.1, hz.2.2⟩)).comp z (hfst.prodMk ((hc hz.2.1).comp z hsnd))).snd
  have hd {z : ℝ × EuclideanSpace ℝ (Fin n)}
      (hz : z.1 ∈ Ioo T' T ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U)
      (v : EuclideanSpace ℝ (Fin n)) :
      mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z (0, v) =
        mfderiv (𝓡 n) (𝓡 n) (fun x => (e.toFun (z.1, x)).2) (c.symm z.2)
          (mfderiv (𝓡 n) (𝓡 n) c.symm z.2 v) := by
    rw [← RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))]
    exact congrArg (fun A => A v) (mfderiv_comp z.2
      ((e.spatialMap_contMDiffAt hU hz.1 hz.2.2).mdifferentiableAt (by simp))
      ((hc hz.2.1).mdifferentiableAt (by simp)))
  have hnhds : ∀ᶠ z : ℝ × EuclideanSpace ℝ (Fin n) in 𝓝 p,
      z.1 ∈ Ioo T' T ∧ z.2 ∈ c.target ∧ c.symm z.2 ∈ U := by
    have h₁ := continuousAt_fst.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)
    have h₂ := continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp.1)
    have h₃ := ((hc hp.1).continuousAt.comp continuousAt_snd).preimage_mem_nhds
      (hU.mem_nhds hp.2)
    exact Filter.inter_mem h₁ (Filter.inter_mem h₂ h₃)
  apply (G.flow.contDiffAt_family_pullback_inner (isOpen_Ioo.mem_nhds ht)
    (hf ⟨ht, hp⟩) (0, EuclideanSpace.basisFun (Fin n) ℝ a)
      (0, EuclideanSpace.basisFun (Fin n) ℝ b)).congr_of_eventuallyEq
  filter_upwards [hnhds] with z hz
  dsimp [FlowCarrier.coordinateCoefficient, pullbackInnerValue]
  rw [hd hz, hd hz]
  rfl

end SmoothSpacetimeEmbedding

end PoincareConjecture
