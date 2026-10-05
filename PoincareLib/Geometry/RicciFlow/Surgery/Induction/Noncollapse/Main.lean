import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.GuardedVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.ConfigurationTransfer
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.Confinement.CapAvoidance
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.FinalAssembly

/-!
# M46 noncollapsing induction through controlled surgery

Morgan--Tian Proposition 16.1 and Remark 16.2, pp. 367-394.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Every calibrated setup carrying its selected Proposition 16.5 persistence
package has a noncollapsing extension at each compatible finite prefix.
The common positive kappa is selected from the old prefix and Theorem 8.1
before the next surgery radius; the positive cutoff is selected afterward
and before the observed flow. It is at most the previous prefix cutoff.

The proof uses M45's stored cap-persistence package on the actual M33
history. Positive-action barriers exclude the cap windows and give compact
confinement. A finite-gauge direct method attains the actual action infimum;
free-endpoint variation and the capped slice-value comparison supply
Proposition 16.4's minimizing region. Claim 16.27's old seed cylinder,
comparison paths and full-measure stable image provide the M15 configuration.
The half-radius estimate retains the factor 1/8. Canonical volume and the
smaller-radius cylinder handle the other radius cases. Positive-component
propagation preserves Remark 16.2's exemption throughout the same `[0,O.H)`.

All geometric producers are proved in the owned helper tree and substituted
below. The published predecessor argument and conclusion are unchanged.
Source: Morgan--Tian Proposition 16.1 and Remark 16.2, pp. 367-394;
Theorem 8.1, pp. 169-176. The precise constant order and producer derivations
are recorded in proof-work/tasks/M46/derivations/.
-/

/-- Proposition 16.1 with Remark 16.2's positive-component exemption,
proved using the supplied analytic predecessors and stored cap data. -/
theorem repairedNoncollapseInduction (predecessors : M46Predecessors.{u}) :
    RepairedNoncollapseInductionTheory.{u} := by
  refine ⟨fun S => ?_⟩
  exact Proofs.M46.induction_of_actionBarrierProducer predecessors S
    (Proofs.M46.capAvoidanceProducer_of_parameters predecessors S)

end PoincareMT
