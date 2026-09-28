import PoincareConjecture.Proofs.M48.StaticCap
import PoincareConjecture.Proofs.M48.StaticComponents
import PoincareConjecture.Proofs.M48.StrongNeck









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture


theorem M33RegularHistoryData.canonical_control
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (t : ℝ) (ht : t ∈ H.generalized.interval) (hregular : t ∉ F.surgery_times)
    (x : (H.generalized.slice t).carrier) {epsilon C : ℝ}
    (hcanonical : SurgeryCanonicalControl F t (H.history.forward t ht x) epsilon C) :
    GeneralizedCanonicalControl (F := H.generalized) t x epsilon C := by
  let e := H.regularDiffeomorph t ht hregular
  have he : MetricHomothety (H.generalized.metric t) (F.metric t) e 1 := by
    intro y v w
    change (F.metric t).inner (H.history.forward t ht y)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y v)
      (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) y w) =
        1 * (H.generalized.metric t).inner y v w
    rw [one_mul]
    exact H.history.metric_pullback t ht y v w
  have K := m13.metric_homothety _ _ (H.generalized.metric t) (F.metric t)
    e 1 zero_lt_one he
  cases hcanonical with
  | neck N hcenter => exact H.canonical_neck ht N hregular C x hcenter
  | cap N hepsilon hconstant _ hcore =>
    exact .cap (N.m48_pullback he K (H.generalized.connection t))
      hepsilon hconstant rfl hcore
  | component N hx =>
    exact .component (N.m48_pullback he K (H.generalized.connection t)) hx
  | round N hx => exact .round (N.m48_pullback he) hx

end PoincareConjecture
