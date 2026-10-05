import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/EuclideanBox.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Volume of Euclidean coordinate boxes

The coordinate integration used to expand Morgan-Tian Lemma 17.12,
p. 410, uses the standard Euclidean volume. Mathlib's volume-preserving
identification with a finite function space gives the box formula,
including empty coordinate intervals and dimension zero.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace EuclideanSpace

/-- Euclidean coordinate-box volume is the product of interval lengths,
as used in the neck-volume argument of MT Lemma 17.12, p. 410. -/
theorem volume_coordinate_Ioo {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    volume {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Ioo (a i) (b i)} =
      ∏ i, ENNReal.ofReal (b i - a i) := by
  have hset : {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Ioo (a i) (b i)} =
      WithLp.ofLp ⁻¹' (pi univ (fun i => Ioo (a i) (b i))) := by
    ext x
    simp
  rw [hset, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet,
    Real.volume_pi_Ioo]

end EuclideanSpace
