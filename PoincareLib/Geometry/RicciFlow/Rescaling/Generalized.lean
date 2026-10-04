import PoincareLib.Geometry.Spacetime.Rescaling.Assembly
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Rescaling.ProductComparison
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
# Generalized parabolic rescaling

The affine clock, metric homothety, and actual domain transports assemble into
the complete rescaling theory from the supplied generalized Ricci gauge theory.
The ordinary construction allows an empty carrier; only the comparison of
supplied ordinary-product realizations assumes a nonempty carrier.

Adapted from `PoincareMT/Proofs/M13.lean` at source revision
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`.
See Morgan--Tian, Definition 3.40, p. 61; Definitions 3.38 and 3.41,
pp. 61-62; Theorem 1.2 and Definitions 1.4-1.8, pp. 3-7;
Lemma 6.72 and Corollary 6.74, pp. 141-142; Definition 9.1, p. 180,
and Section 9.2.1, p. 185.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The complete positive parabolic-rescaling theory, including dimension zero,
exact affine domains, endpoint derivatives, all homothety fields, and the
comparison of any supplied ordinary-product realizations. -/
theorem generalizedParabolicRescaling (n : ℕ)
    (hEquation : GeneralizedRicciGaugeTheory.{u} n) :
    GeneralizedParabolicRescalingTheory.{u} n := by
  refine {
    rescale := ?_
    metric_homothety := ?_
    coordinate_metric_homothety := ?_
    ordinary_flow := ?_
    ordinary_product_comparison := ?_ }
  · intro X _ A R Q hQ a
    exact ⟨ParabolicRescaling.generalizedRescaling hEquation R Q hQ a⟩
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact Homothety.metricHomothetyCalculus g h f Q hQ hf
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact Homothety.metricHomothetyCalculus g h f Q hQ hf
  · intro M _ _ _ _ _ I F Q hQ a
    exact ParabolicRescaling.ordinaryParabolicRescaling I F Q hQ a
  · intro M _ _ _ _ I F Q hQ a R source target
    exact ParabolicRescaling.ordinaryParabolicProductComparison F Q hQ a R source target

end PoincareMT
