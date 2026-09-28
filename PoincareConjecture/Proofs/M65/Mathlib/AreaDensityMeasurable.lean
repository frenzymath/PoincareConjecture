import PoincareConjecture.Proofs.M65.Mathlib.ChartJacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65AreaDensity_aestronglyMeasurable_in_chart
    (g : RiemannianMetric n M) (p : M) {f : LoopPlane → M} {domain : Set LoopPlane}
    (hdomain : MeasurableSet domain) (hf : ContinuousOn f domain)
    (hmap : MapsTo f domain (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hdf : ∀ᵐ z ∂volume.restrict domain, MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    AEStronglyMeasurable (m60AreaDensity g f) (volume.restrict domain) := by
  classical
  let chi := chartAt (EuclideanSpace ℝ (Fin n)) p
  let U : Set (EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
    Prod.fst ⁻¹' chi.target
  let J := U.piecewise (m65ChartJacobian g p) (fun _ => 0)
  have hJ : Measurable J := (m65ChartJacobian_continuousOn g p).measurable_piecewise
    continuous_const.continuousOn (chi.open_target.preimage continuous_fst).measurableSet
  have hcoord : AEMeasurable (chi ∘ f) (volume.restrict domain) :=
    (chi.continuousOn.comp hf hmap).aemeasurable hdomain
  have hdata : AEMeasurable (fun z => (chi (f z), fderiv ℝ (chi ∘ f) z))
      (volume.restrict domain) := hcoord.prodMk (measurable_fderiv ℝ (chi ∘ f)).aemeasurable
  have hmeas := (hJ.comp_aemeasurable hdata).aestronglyMeasurable
  apply hmeas.congr
  filter_upwards [hdf, ae_restrict_mem hdomain] with z hz hzd
  have htarget : (chi (f z), fderiv ℝ (chi ∘ f) z) ∈ U := chi.map_source (hmap hzd)
  dsimp only [J, Function.comp_apply]
  rw [Set.piecewise_eq_of_mem U _ _ htarget]
  exact (m65AreaDensity_eq_chartJacobian g p hz (hmap hzd)).symm




theorem m65AreaDensity_aestronglyMeasurable
    (g : RiemannianMetric n M) {f : LoopPlane → M} {domain : Set LoopPlane}
    (hcompact : IsCompact domain) (hf : ContinuousOn f domain)
    (hdf : ∀ᵐ z ∂volume, z ∈ domain → MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    AEStronglyMeasurable (m60AreaDensity g f) (volume.restrict domain) := by
  classical
  obtain ⟨centers, hcover⟩ := (hcompact.image_of_continuousOn hf).elim_finite_subcover
    (fun p : M => (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (fun p => (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source)
    (fun y _ => mem_iUnion.mpr ⟨y, mem_chart_source _ y⟩)
  let pieces : centers → Set LoopPlane := fun p => domain ∩
    f ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) p.1).source
  have hpieces (p : centers) : MeasurableSet (pieces p) := by
    obtain ⟨U, hU, hEq⟩ := continuousOn_iff'.mp hf _
      (chartAt (EuclideanSpace ℝ (Fin n)) p.1).open_source
    change MeasurableSet (domain ∩ f ⁻¹' _)
    rw [inter_comm, hEq]
    exact hU.measurableSet.inter hcompact.measurableSet
  have hlocal (p : centers) :
      AEStronglyMeasurable (m60AreaDensity g f) (volume.restrict (pieces p)) := by
    apply m65AreaDensity_aestronglyMeasurable_in_chart g p.1 (hpieces p)
      (hf.mono inter_subset_left) (fun _ hz => hz.2)
    filter_upwards [ae_restrict_of_ae hdf, ae_restrict_mem (hpieces p)] with z hz hzp
    exact hz hzp.1
  have hEq : domain = ⋃ p : centers, pieces p := by
    ext z
    constructor
    · intro hz
      have h := hcover (mem_image_of_mem f hz)
      simp only [mem_iUnion] at h
      obtain ⟨p, hp, hzp⟩ := h
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hz, hzp⟩
    · intro hz
      obtain ⟨p, hp⟩ := mem_iUnion.mp hz
      exact hp.1
  rw [hEq]
  exact AEStronglyMeasurable.iUnion hlocal

end PoincareConjecture
