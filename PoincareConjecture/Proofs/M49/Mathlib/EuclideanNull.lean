import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic









set_option autoImplicit false

open Set MeasureTheory

namespace EuclideanSpace



theorem volume_coordinate_hyperplane {ι : Type*} [Fintype ι] (i : ι) (a : ℝ) :
    volume {x : EuclideanSpace ℝ ι | x i = a} = 0 := by
  have hset : {x : EuclideanSpace ℝ ι | x i = a} =
      WithLp.ofLp ⁻¹' {x : ι → ℝ | x i = a} := rfl
  rw [hset, (PiLp.volume_preserving_ofLp ι).measure_preimage
    ((isClosed_eq (continuous_apply i) continuous_const).measurableSet.nullMeasurableSet)]
  exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i a

end EuclideanSpace
