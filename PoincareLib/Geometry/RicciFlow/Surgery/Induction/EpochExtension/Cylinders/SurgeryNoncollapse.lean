import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularNoncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.Transport.HistoryNoncollapse

/-!
# M15 noncollapse on the actual surgery flow

Compose the two checked transfers on the retained geometry and history.
The premise still requires the actual M15 estimate at the tested preimage
points. The source's exception uses the original surgery components.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem M48Predecessors.surgery_noncollapsedOn
    (P : M48Predecessors.{u}) {F : SurgeryFlowData.{u}} {T : ℝ}
    {L : RepairedPreterminalSlab F T} (R : M48RegularSpacetimeData L)
    {J : Set ℝ} (hJ : J ⊆ R.history.generalized.interval) (kappa : ℝ)
    (hN : ∀ t ∈ J, ∀ ht : t ∈ R.history.generalized.interval,
      ∀ z : (R.history.generalized.slice t).carrier,
        ¬ SurgeryPositiveComponentAt F t (R.history.history.forward t ht z) →
          M15GeneralizedNoncollapseAt R.geometry.toLGeometry
            (⟨t, z⟩ : R.history.generalized.point) F.parameters.epsilon kappa) :
    SurgeryNoncollapsedOn F J kappa :=
  R.history.noncollapsedOn_of_generalized hJ kappa
    (fun t ht htime z hpositive => P.regular_noncollapsed R ⟨t, z⟩ F.parameters.epsilon
      kappa (hN t ht htime z hpositive))

end PoincareMT
