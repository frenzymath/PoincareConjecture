import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.RelativeDensity.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem contMDiffAt_relativeVolumeDensity
    (F : RicciFlow n M J) (h : RiemannianMetric n M)
    {t : ℝ} (ht : t ∈ interior J) (p : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => (F.metric z.1).relativeVolumeDensity h z.2) (t, p) := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hp : p ∈ e.target := mem_chart_source _ p
  have hx : e.symm p ∈ e.source := e.map_target hp
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hf := F.contDiffAt_pullbackVolumeDensity_spacetime ht
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hh := h.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)
  have hden : ContDiffAt ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      h.pullbackVolumeDensity e z.2) (t, e.symm p) :=
    ContDiffAt.comp (g := h.pullbackVolumeDensity e)
      (f := fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.2)
      (t, e.symm p) hh.1 contDiffAt_snd
  have hquot : ContDiffAt ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric z.1).pullbackVolumeDensity e z.2 / h.pullbackVolumeDensity e z.2)
      (t, e.symm p) := hf.div hden hh.2.ne'
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞
      (fun z : ℝ × M => (z.1, e.symm z.2)) (t, p) :=
    contMDiffAt_fst.prodMk_space
      ((hei.contMDiffAt (e.open_target.mem_nhds hp)).comp (t, p) contMDiffAt_snd)
  apply (hquot.contMDiffAt.comp (t, p) hcoord).congr_of_eventuallyEq
  filter_upwards [(continuous_snd.tendsto (t, p)) (e.open_target.mem_nhds hp)] with z hz
  symm
  change (F.metric z.1).pullbackVolumeDensity e (e.symm z.2) /
      h.pullbackVolumeDensity e (e.symm z.2) =
    (F.metric z.1).relativeVolumeDensity h z.2
  rw [← (F.metric z.1).relativeVolumeDensity_eq_pullback_div h e (e.symm z.2)
    (hD.mfderiv_injective (e.map_target hz)), e.right_inv hz]

theorem contMDiffOn_relativeVolumeDensity
    (F : RicciFlow n M J) (h : RiemannianMetric n M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => (F.metric z.1).relativeVolumeDensity h z.2)
      (interior J ×ˢ univ) :=
  fun z hz => (F.contMDiffAt_relativeVolumeDensity h hz.1 z.2).contMDiffWithinAt

theorem hasDerivAt_relativeVolumeDensity
    (F : RicciFlow n M J) (h : RiemannianMetric n M)
    {t : ℝ} (ht : t ∈ interior J) (p : M) :
    HasDerivAt (fun s => (F.metric s).relativeVolumeDensity h p)
      (-(F.connection t).scalarCurvature p * (F.metric t).relativeVolumeDensity h p) t := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hp : p ∈ e.target := mem_chart_source _ p
  have hx : e.symm p ∈ e.source := e.map_target hp
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hval (s : ℝ) : (F.metric s).relativeVolumeDensity h p =
      (F.metric s).pullbackVolumeDensity e (e.symm p) /
        h.pullbackVolumeDensity e (e.symm p) := by
    rw [← (F.metric s).relativeVolumeDensity_eq_pullback_div h e (e.symm p)
      (hD.mfderiv_injective hx), e.right_inv hp]
  have hd := (F.hasDerivAt_pullbackVolumeDensity ht
    (F.connection t).intrinsicCurvatureTensorCalculus e (e.symm p)
    (hD.mfderiv_injective hx)).div_const (h.pullbackVolumeDensity e (e.symm p))
  rw [e.right_inv hp] at hd
  have hcoeff : -(F.connection t).scalarCurvature p *
      (F.metric t).relativeVolumeDensity h p =
      (-(F.connection t).scalarCurvature p *
        (F.metric t).pullbackVolumeDensity e (e.symm p)) /
          h.pullbackVolumeDensity e (e.symm p) := by
    rw [hval t]
    ring
  rw [hcoeff, show (fun s => (F.metric s).relativeVolumeDensity h p) =
    (fun s => (F.metric s).pullbackVolumeDensity e (e.symm p) /
      h.pullbackVolumeDensity e (e.symm p)) from funext hval]
  exact hd

theorem volumeMeasure_eq_reference_withDensity
    [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (h : RiemannianMetric n M) (t : ℝ) :
    (F.metric t).volumeMeasure = h.volumeMeasure.withDensity
      (fun x => ENNReal.ofReal ((F.metric t).relativeVolumeDensity h x)) :=
  (F.metric t).volumeMeasure_eq_withDensity_relativeVolumeDensity h

end PoincareConjecture.RicciFlow
