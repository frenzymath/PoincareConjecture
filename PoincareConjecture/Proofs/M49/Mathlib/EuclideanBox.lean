import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic










set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace EuclideanSpace



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
