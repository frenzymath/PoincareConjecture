import PoincareConjecture.Proofs.M60.Mathlib.PullbackMetricRegularity
import PoincareConjecture.Proofs.M60.Mathlib.CoordinateDerivative
import PoincareConjecture.Proofs.M60.Mathlib.LocalAlmostEverywhere
import PoincareConjecture.Definitions.M60Area
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_aestronglyMeasurable_in_chart (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hmaps : MapsTo f U e.source) (i j : Fin 2) :
    AEStronglyMeasurable (fun z => m60AreaGram g f z i j) (volume.restrict U) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let B := fun p : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    g.inner (e.symm p.1)
      (mfderiv (𝓡 n) (𝓡 n) e.symm p.1 p.2.1)
      (mfderiv (𝓡 n) (𝓡 n) e.symm p.1 p.2.2)
  let V := e.target ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  let B' := V.piecewise B (fun _ => (0 : ℝ))
  have hB : ContinuousOn B V := M60.continuousOn_pullback_inner e.open_target hei
  have hB' : Measurable B' := hB.measurable_piecewise continuous_const.continuousOn
    (e.open_target.prod isOpen_univ).measurableSet
  have hp : AEMeasurable (e ∘ f) (volume.restrict U) :=
    (e.continuousOn.comp hf hmaps).aemeasurable hU.measurableSet
  have hd (k : Fin 2) : Measurable (fun z : LoopPlane =>
      fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ k)) :=
    measurable_fderiv_apply_const ℝ (e ∘ f) _
  have hm := (hB'.comp_aemeasurable
    (hp.prodMk ((hd i).aemeasurable.prodMk (hd j).aemeasurable))).aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  have hsrc := hmaps hz
  have hpoint : e.symm (e (f z)) = f z := e.left_inv hsrc
  have hinner (v w : EuclideanSpace ℝ (Fin n)) :
      g.inner (e.symm (e (f z))) v w = g.inner (f z) v w :=
    congrArg (fun p : M => g.inner p v w) hpoint
  have hdf := M60.mfderiv_eq_inverse_chart_comp_fderiv e he
    ((hf z hz).continuousAt (hU.mem_nhds hz)) hsrc
  change B' ((e ∘ f) z,
    fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i),
    fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) = _
  have hV : ((e ∘ f) z,
      fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i),
      fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) ∈ V :=
    ⟨e.map_source hsrc, mem_univ _⟩
  rw [show B' = V.piecewise B (fun _ => 0) from rfl,
    piecewise_eq_of_mem _ _ _ hV]
  simp only [B, Function.comp_apply, m60AreaGram, hdf, hinner]
  rfl

theorem m60AreaDensity_aestronglyMeasurable_in_chart (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hmaps : MapsTo f U e.source) :
    AEStronglyMeasurable (m60AreaDensity g f) (volume.restrict U) := by
  have hG := m60AreaGram_aestronglyMeasurable_in_chart g e he hei hU hf hmaps
  have hdet := ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hmax := (show Continuous (fun x : ℝ => max 0 x) from
    continuous_const.max continuous_id).comp_aestronglyMeasurable hdet
  change AEStronglyMeasurable (fun z => m60AreaDensity g f z) (volume.restrict U)
  simpa [m60AreaDensity, Matrix.det_fin_two] using
    Real.continuous_sqrt.comp_aestronglyMeasurable hmax

theorem m60AreaDensity_aestronglyMeasurableOn (g : RiemannianMetric n M)
    {f : LoopPlane → M} {S : Set LoopPlane} (hS : IsOpen S) (hf : ContinuousOn f S) :
    AEStronglyMeasurable (m60AreaDensity g f) (volume.restrict S) := by
  apply M60.aestronglyMeasurable_restrict_of_locally volume
    (HereditarilyLindelofSpace.isLindelof S)
  intro x hx
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let U := S ∩ f ⁻¹' e.source
  have hU : IsOpen U := hf.isOpen_inter_preimage hS e.open_source
  have hxU : x ∈ U := ⟨hx, mem_chart_source _ _⟩
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  exact m60AreaDensity_aestronglyMeasurable_in_chart g e (mdifferentiable_chart (f x))
    contMDiffOn_chart_symm hU (hf.mono inter_subset_left) (fun _ hy => hy.2)

end PoincareConjecture
