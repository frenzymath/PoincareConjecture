import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite basis coordinates and Euclidean volume

The source-coordinate measure bridge for Morgan-Tian Lemma 6.71, p. 141.
Forgetting the Euclidean L2 wrapper preserves volume, so a finite basis
gives the same coordinate measure from either Euclidean or function coordinates.
-/

set_option autoImplicit false

namespace Module.Basis

variable {ι : Type*} [Fintype ι] {V : Type*}
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

/-- Euclidean coordinates in an arbitrary finite real basis, as used for
the source measure in Morgan-Tian Lemma 6.71, p. 141. -/
noncomputable def euclideanCoordinates (b : Module.Basis ι ℝ V) :
    EuclideanSpace ℝ ι ≃L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).trans
    b.equivFun.symm.toContinuousLinearEquiv

/-- The Euclidean coordinate map sends each standard basis vector to the
specified basis vector, as required in Lemma 6.71, p. 141. -/
theorem euclideanCoordinates_basis (b : Module.Basis ι ℝ V) (i : ι) :
    b.euclideanCoordinates (EuclideanSpace.basisFun ι ℝ i) = b i := by
  classical
  change b.equivFun.symm (WithLp.ofLp (EuclideanSpace.basisFun ι ℝ i)) = b i
  apply b.equivFun.injective
  ext j
  simp [Module.Basis.equivFun_self]

/-- Euclidean and finite-function coordinates induce exactly the same
basis volume, including dimension zero, in Morgan-Tian Lemma 6.71, p. 141. -/
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

/-- Integrability in basis coordinate volume is equivalent to integrability
in Euclidean coordinates on the exact preimage, Lemma 6.71, p. 141. -/
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

/-- Basis coordinate volume transports the restricted Bochner integral
through the same Euclidean coordinates, Morgan-Tian Lemma 6.71, p. 141. -/
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
