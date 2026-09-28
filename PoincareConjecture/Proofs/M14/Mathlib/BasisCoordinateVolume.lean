import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

namespace Module.Basis

variable {ι : Type*} [Fintype ι] {V : Type*}
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

noncomputable def euclideanCoordinates (b : Module.Basis ι ℝ V) :
    EuclideanSpace ℝ ι ≃L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).trans
    b.equivFun.symm.toContinuousLinearEquiv

theorem euclideanCoordinates_basis (b : Module.Basis ι ℝ V) (i : ι) :
    b.euclideanCoordinates (EuclideanSpace.basisFun ι ℝ i) = b i := by
  classical
  change b.equivFun.symm (WithLp.ofLp (EuclideanSpace.basisFun ι ℝ i)) = b i
  apply b.equivFun.injective
  ext j
  simp [Module.Basis.equivFun_self]

theorem map_euclideanCoordinates_volume [MeasurableSpace V] [BorelSpace V]
    (b : Module.Basis ι ℝ V) :
    MeasureTheory.Measure.map b.euclideanCoordinates MeasureTheory.volume =
      MeasureTheory.Measure.map b.equivFun.symm MeasureTheory.volume := by
  change MeasureTheory.Measure.map (b.equivFun.symm ∘ WithLp.ofLp)
    MeasureTheory.volume = _
  have hm : Measurable (b.equivFun.symm : (ι → ℝ) → V) :=
    b.equivFun.symm.toContinuousLinearEquiv.continuous.measurable
  rw [← MeasureTheory.Measure.map_map hm
    (PiLp.volume_preserving_ofLp ι).measurable,
    (PiLp.volume_preserving_ofLp ι).map_eq]

theorem integrableOn_coordinateVolume_iff [MeasurableSpace V] [BorelSpace V]
    {F : Type*} [NormedAddCommGroup F] (b : Module.Basis ι ℝ V)
    (f : V → F) (S : Set V) :
    MeasureTheory.IntegrableOn f S
        (MeasureTheory.Measure.map b.equivFun.symm MeasureTheory.volume) ↔
      MeasureTheory.IntegrableOn (f ∘ b.euclideanCoordinates)
        (b.euclideanCoordinates ⁻¹' S) MeasureTheory.volume := by
  let e := b.euclideanCoordinates.toHomeomorph.toMeasurableEquiv
  rw [← b.map_euclideanCoordinates_volume]
  change MeasureTheory.Integrable f
    ((MeasureTheory.volume.map e).restrict S) ↔
      MeasureTheory.Integrable (f ∘ e) (MeasureTheory.volume.restrict (e ⁻¹' S))
  rw [e.restrict_map, MeasureTheory.integrable_map_equiv]

theorem setIntegral_coordinateVolume [MeasurableSpace V] [BorelSpace V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Module.Basis ι ℝ V) (f : V → F) (S : Set V) :
    (∫ y in S, f y ∂MeasureTheory.Measure.map b.equivFun.symm MeasureTheory.volume) =
      ∫ z in b.euclideanCoordinates ⁻¹' S, (f ∘ b.euclideanCoordinates) z := by
  let e := b.euclideanCoordinates.toHomeomorph.toMeasurableEquiv
  rw [← b.map_euclideanCoordinates_volume]
  change (∫ y, f y ∂(MeasureTheory.volume.map e).restrict S) =
    ∫ z, f (e z) ∂MeasureTheory.volume.restrict (e ⁻¹' S)
  rw [e.restrict_map, MeasureTheory.integral_map_equiv]

end Module.Basis
