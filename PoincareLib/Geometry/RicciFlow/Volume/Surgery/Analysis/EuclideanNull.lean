import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/EuclideanNull.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Null Euclidean coordinate hyperplanes

The boundary argument in Morgan-Tian Lemma 17.12, p. 410, uses
the zero volume of coordinate hyperplanes. Transport Mathlib's
finite-product measure statement to the actual Euclidean volume.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace EuclideanSpace

/-- A coordinate hyperplane has Euclidean volume zero, as used for
the neck boundary in MT Lemma 17.12, p. 410. -/
theorem volume_coordinate_hyperplane {ι : Type*} [Fintype ι] (i : ι) (a : ℝ) :
    volume {x : EuclideanSpace ℝ ι | x i = a} = 0 := by
  have hset : {x : EuclideanSpace ℝ ι | x i = a} =
      WithLp.ofLp ⁻¹' {x : ι → ℝ | x i = a} := rfl
  rw [hset, (PiLp.volume_preserving_ofLp ι).measure_preimage
    ((isClosed_eq (continuous_apply i) continuous_const).measurableSet.nullMeasurableSet)]
  exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i a

end EuclideanSpace
