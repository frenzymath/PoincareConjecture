import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Proofs.M12
import PoincareConjecture.Proofs.M13.Rescaling
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M13.OrdinaryProduct









set_option autoImplicit false

universe u

namespace PoincareConjecture































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
    exact ⟨M13.generalizedRescaling hEquation R Q hQ a⟩
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact M13.metricHomothetyCalculus g h f Q hQ hf
  · intro M N _ _ _ _ _ _ _ _ _ _ _ _ g h f Q hQ hf
    exact M13.metricHomothetyCalculus g h f Q hQ hf
  · intro M _ _ _ _ _ I F Q hQ a
    exact M13.ordinaryParabolicRescaling I F Q hQ a
  · intro M _ _ _ _ I F Q hQ a R source target
    exact M13.ordinaryParabolicProductComparison F Q hQ a R source target







theorem generalizedParabolicRescaling_from_M12 (n : ℕ) :
    GeneralizedParabolicRescalingTheory.{u} n :=
  generalizedParabolicRescaling n (generalizedRicciGaugeGeometry_from_M03_M04_M11 n)

end PoincareConjecture
