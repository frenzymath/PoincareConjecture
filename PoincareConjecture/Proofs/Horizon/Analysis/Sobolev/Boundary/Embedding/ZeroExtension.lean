import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration








set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryEmbedding

open Weak BoundaryTangential Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem memW1p_zeroExtension {p : ℝ≥0∞} (hp : 1 ≤ p) {u : E → ℝ}
    (hu0 : MemW01p 2 u (halfSpace d)) (hu : MemW1p p u (halfSpace d)) :
    MemW1p p ((halfSpace d).indicator u) univ := by
  let g (i : Fin d) := chosenWeakPartial' 2 i u (halfSpace d)
  have hg2 (i : Fin d) : MemLp (g i) 2 (volume.restrict (halfSpace d)) :=
    chosenWeakPartial'_memLp_of_mem hu0.1 i
  have hgp (i : Fin d) : MemLp (g i) p (volume.restrict (halfSpace d)) := by
    have hae := EuclideanEmbedding.EuclideanIterated.chosenWeakPartial'_cross_exponent_ae_eq
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hp isOpen_halfSpace hu0.1 hu i
    exact (chosenWeakPartial'_memLp_of_mem hu i).ae_eq hae.symm
  let w : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u (halfSpace d) :=
    { memLp := by simpa using hu0.1.1
      weakGrad := fun x => WithLp.toLp 2 (fun i => g i x)
      weakGrad_component_memLp := fun i => by simpa using hg2 i
      isWeakGrad := fun i => chosenWeakPartial'_isWeakPartial_of_mem hu0.1 i }
  have hu0' : MemW01p (ENNReal.ofReal (2 : ℝ)) u (halfSpace d) := by simpa using hu0
  have hweak (i : Fin d) : HasWeakPartialDeriv i ((halfSpace d).indicator (g i))
      ((halfSpace d).indicator u) univ :=
    (zeroExtendMemW1pWitnessP isOpen_halfSpace (by norm_num : (1 : ℝ) < 2) hu0' w).isWeakGrad i
  refine ⟨?_, fun i => ⟨(halfSpace d).indicator (g i), ?_, hweak i⟩⟩
  · simpa only [Measure.restrict_univ] using
      (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu.1
  · simpa only [Measure.restrict_univ] using
      (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hgp i)

end Poincare.Analysis.Sobolev.BoundaryEmbedding
