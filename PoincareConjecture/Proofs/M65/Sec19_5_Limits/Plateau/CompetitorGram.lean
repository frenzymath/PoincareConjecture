import PoincareConjecture.Proofs.M65.Mathlib.ChartJacobian
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65AreaGram_posSemidef (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : (m60AreaGram g f z).PosSemidef := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Matrix.posSemidef_gram ℝ (fun i : Fin 2 =>
    mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))

private theorem areaGram_eq_chart (g : RiemannianMetric n M) (p : M)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hz : f z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m60AreaGram g f z = fun i j =>
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f z))
        (fderiv ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) z
          (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
  let chi := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hc : MDifferentiableAt (𝓡 2) (𝓡 n) (chi ∘ f) z :=
    (mdifferentiableAt_atlas (chart_mem_atlas _ _) hz).comp z hf
  have hi : MDifferentiableAt (𝓡 n) (𝓡 n) chi.symm (chi (f z)) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) (chi.map_source hz)
  have heq : chi.symm ∘ (chi ∘ f) =ᶠ[𝓝 z] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (chi.open_source.mem_nhds hz)] with x hx
    exact chi.left_inv hx
  have hd : mfderiv (𝓡 2) (𝓡 n) f z =
      (mfderiv (𝓡 n) (𝓡 n) chi.symm (chi (f z))).comp (fderiv ℝ (chi ∘ f) z) := by
    rw [← heq.mfderiv_eq, mfderiv_comp z hi hc, mfderiv_eq_fderiv]
    rfl
  unfold m60AreaGram RiemannianMetric.pullbackCoefficients
  dsimp only
  rw [chi.left_inv hz]
  ext i j
  rw [hd]
  rfl

private theorem areaGram_aestronglyMeasurable_in_chart
    (g : RiemannianMetric n M) (p : M) {f : LoopPlane → M} {domain : Set LoopPlane}
    (hdomain : MeasurableSet domain) (hf : ContinuousOn f domain)
    (hmap : MapsTo f domain (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hdf : ∀ᵐ z ∂volume.restrict domain, MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    AEStronglyMeasurable (m60AreaGram g f) (volume.restrict domain) := by
  classical
  let chi := chartAt (EuclideanSpace ℝ (Fin n)) p
  let U : Set (EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
    Prod.fst ⁻¹' chi.target
  let J := fun d : EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
    fun i j : Fin 2 => g.pullbackCoefficients chi.symm d.1
      (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ j))
  have hcoeff : ContinuousOn (g.pullbackCoefficients chi.symm) chi.target := by
    intro x hx
    have hs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ chi.symm x :=
      (contMDiffOn_chart_symm (I := 𝓡 n)).contMDiffAt (chi.open_target.mem_nhds hx)
    exact (g.contDiffAt_pullbackCoefficients hs).continuousAt.continuousWithinAt
  have hJ : ContinuousOn J U := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact ((hcoeff.comp continuous_fst.continuousOn (fun _ h => h)).clm_apply
      ((continuous_snd.clm_apply continuous_const).continuousOn)).clm_apply
      ((continuous_snd.clm_apply continuous_const).continuousOn)
  let Jext := U.piecewise J (fun _ => 0)
  have hJext : Measurable Jext := hJ.measurable_piecewise
    continuous_const.continuousOn (chi.open_target.preimage continuous_fst).measurableSet
  have hcoord : AEMeasurable (chi ∘ f) (volume.restrict domain) :=
    (chi.continuousOn.comp hf hmap).aemeasurable hdomain
  have hdata : AEMeasurable (fun z => (chi (f z), fderiv ℝ (chi ∘ f) z))
      (volume.restrict domain) := hcoord.prodMk (measurable_fderiv ℝ (chi ∘ f)).aemeasurable
  apply (hJext.comp_aemeasurable hdata).aestronglyMeasurable.congr
  filter_upwards [hdf, ae_restrict_mem hdomain] with z hz hzd
  dsimp only [Jext, Function.comp_apply]
  rw [Set.piecewise_eq_of_mem U _ _ (chi.map_source (hmap hzd))]
  exact (areaGram_eq_chart g p hz (hmap hzd)).symm

theorem m65AreaGram_aestronglyMeasurable
    (g : RiemannianMetric n M) {f : LoopPlane → M} {domain : Set LoopPlane}
    (hcompact : IsCompact domain) (hf : ContinuousOn f domain)
    (hdf : ∀ᵐ z ∂volume, z ∈ domain → MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    AEStronglyMeasurable (m60AreaGram g f) (volume.restrict domain) := by
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
      AEStronglyMeasurable (m60AreaGram g f) (volume.restrict (pieces p)) := by
    apply areaGram_aestronglyMeasurable_in_chart g p.1 (hpieces p)
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
