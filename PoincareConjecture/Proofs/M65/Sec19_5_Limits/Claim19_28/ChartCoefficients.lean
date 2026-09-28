import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ScalarEvolution
import PoincareConjecture.Proofs.M04.ShiParallelFrames









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b))



noncomputable def m65FlowChartMetric (p : M) (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  M04.shiChartMetric (F.metric z.1) (chartAt (EuclideanSpace ℝ (Fin n)) p) z.2



noncomputable def m65FlowChartRicci (p : M) (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (-1 / 2 : ℝ) • fderiv ℝ (m65FlowChartMetric F p) z (1, 0)



theorem m65FlowChartMetric_contDiffOn (p : M) :
    ContDiffOn ℝ ∞ (m65FlowChartMetric F p)
      (Ioo a b ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  let S := Ioo a b ×ˢ e.target
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞
      (fun z : ℝ × E => e.symm z.2) S :=
    hi.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
  have hparam : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : ℝ × E => (z.1, e.symm z.2)) S :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk hbase
  have hmetric := F.smooth.comp hparam
    (fun z hz => ⟨Ioo_subset_Icc_self hz.1, mem_univ (e.symm z.2)⟩)
  have hfield (v : E) : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n).tangent ∞
      (fun z : ℝ × E => (⟨e.symm z.2, M04.shiChartField e v (e.symm z.2)⟩ :
        TangentBundle (𝓡 n) M)) S :=
    (M04.shiChartField_smooth he hi v).comp hbase (fun _ hz => e.map_target hz.2)
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w z hz
  have hpair : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun y : ℝ × E => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (e.symm y.2)
        ((F.metric y.1).inner (e.symm y.2) (M04.shiChartField e v (e.symm y.2))
          (M04.shiChartField e w (e.symm y.2)))) S z :=
    (hmetric z hz).clm_bundle_apply₂ (hfield v z hz) (hfield w z hz)
  have hscalar := (Bundle.contMDiffWithinAt_totalSpace.mp hpair).2.contDiffWithinAt
  apply hscalar.congr_of_eventuallyEq_of_mem _ hz
  filter_upwards [self_mem_nhdsWithin] with y hy
  change M04.shiChartMetric (F.metric y.1) e y.2 v w = _
  rw [M04.shiChartField_at_inverse he hi hy.2,
    M04.shiChartField_at_inverse he hi hy.2]
  rfl



theorem m65FlowChartRicci_contDiffOn (p : M) :
    ContDiffOn ℝ ∞ (m65FlowChartRicci F p)
      (Ioo a b ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) := by
  have hdiff : ContDiffOn ℝ ∞ (fderiv ℝ (m65FlowChartMetric F p))
      (Ioo a b ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :=
    (m65FlowChartMetric_contDiffOn F p).fderiv_of_isOpen
      (isOpen_Ioo.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_target) (by simp)
  exact (contDiffOn_const (c := (-1 / 2 : ℝ))).smul
    (hdiff.clm_apply (contDiffOn_const (c := (1, (0 : EuclideanSpace ℝ (Fin n))))))



theorem m65FlowChartMetric_at_source (p : M) (t : ℝ) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (V W : TangentSpace (𝓡 n) q) :
    m65FlowChartMetric F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) q)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q V)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q W) =
      (F.metric t).inner q V W := by
  change M04.shiChartMetric (F.metric t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
    ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q V)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q W) = _
  rw [M04.shiChartMetric_at_source contMDiffOn_chart contMDiffOn_chart_symm hq]
  exact congrArg₂ (fun V W => (F.metric t).inner q V W)
    (Proofs.M09.chartVectorField_differential p q V hq)
    (Proofs.M09.chartVectorField_differential p q W hq)



theorem m65FlowChartRicci_at_source (p : M) {t : ℝ} (ht : t ∈ Ioo a b) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (V W : TangentSpace (𝓡 n) q) :
    m65FlowChartRicci F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) q)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q V)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) q W) =
      (F.connection t).ricci q V W := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let v := mfderiv (𝓡 n) (𝓡 n) e q V
  let w := mfderiv (𝓡 n) (𝓡 n) e q W
  have hz : (t, e q) ∈ Ioo a b ×ˢ e.target := ⟨ht, e.map_source hq⟩
  have hmetric := ((m65FlowChartMetric_contDiffOn F p).contDiffAt
    ((isOpen_Ioo.prod e.open_target).mem_nhds hz)).differentiableAt (by simp)
  have htime : HasDerivAt (fun r => m65FlowChartMetric F p (r, e q))
      (fderiv ℝ (m65FlowChartMetric F p) (t, e q) (1, 0)) t := by
    exact (hmetric.hasFDerivAt.comp t
      ((hasFDerivAt_id t).prodMk (hasFDerivAt_const (e q) t))).hasDerivAt
  have hpair := (htime.clm_apply (hasDerivAt_const t v)).clm_apply
    (hasDerivAt_const t w)
  have heq : (fun r => m65FlowChartMetric F p (r, e q) v w) =
      fun r => (F.metric r).inner q V W := by
    funext r
    exact m65FlowChartMetric_at_source F p r hq V W
  rw [heq] at hpair
  have hflow := (F.equation t (Ioo_subset_Icc_self ht) q V W).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hvalue := hpair.unique hflow
  change (-1 / 2 : ℝ) *
    (fderiv ℝ (m65FlowChartMetric F p) (t, e q) (1, 0) v w) = _
  simp only [map_zero, add_zero] at hvalue
  rw [hvalue]
  ring

end PoincareConjecture
