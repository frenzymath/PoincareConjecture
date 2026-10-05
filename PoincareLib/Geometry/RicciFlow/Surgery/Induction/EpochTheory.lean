import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochData
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.UnifiedTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Service
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M48EpochExtension.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M48 repaired one-step epoch extension statement

Natural-language theorem: fix the predecessor services and a setup
calibrated by the actual M47 component estimate and M45 model estimates,
with their coefficients bounded by the stored M32 selector coefficient and
the cutoff bounds in M48AnalyticCalibration. Choose the M46/M47 packages
for that final setup. For i > 0, let a flow have exact time domain [0,H),
with T_i <= H < T_(i+1) and an actual final smooth slab whose curvature is
unbounded at H. Assume controlled schedule prefix, current canonical and
noncollapsing properties at the selected radius, and the selected parameter
profiles on the full next epoch and overlap. The surgery bridge may redecorate
the observation with the calibrated standard-cap model. There is an actual
extension with surgery at H and an observation
H < H' <= T_(i+1), with no surgery in (H,H'). If H' < T_(i+1), the extended
domain is exactly [0,H') and a preterminal slab starts at H and has singular
frontier H'. Otherwise H' is the epoch boundary; the returned flow need not
end there. Whenever the returned domain ends at H', including equality
with the epoch boundary, it retains that preterminal slab starting at H.

The extension preserves old-prefix controls and has whole-domain
admissibility and pinching. It carries the selected M46 noncollapsing and
M47 canonical properties on the observed interval, and keeps the selected
standard-cap model tied to the returned observation. Scalar time-derivative
control is internal to the M31 application at its auxiliary radius and the
stored analytic coefficient. It is not a premise of Theorem 15.9 or a
separate M48 output. Checked helpers construct the actual surgery input,
apply M33 and observe its maximal restart. The checked M48 assembly then
applies the exact selected M47 and M46 outputs to that same restart, with
the numerical profiles transported through its parameter equality. The M33
terminal operation also exports the checked Definition 15.8 terminal policy
for the newly created event on the singleton interval `{H}`. The extension
retains M33's primitive preservation of old event geometry. Together with
the old flow's policy and the absence of events in (H,H'), these outputs
give policy on [0,H'). They do not create policy for arbitrary old events.

Source: Morgan--Tian, Theorem 15.9 inductive construction and its outline,
printed pp. 363--366, the Chapter 16 noncollapsing step, and the Chapter 17
canonical-neighborhood step and Section 17.2 construction, printed
pp. 409--410. This is one singular extension step. It does not close a
continuation chain or assert local finiteness, a global schedule, or an
endpoint theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! Predecessor interface retained for compatibility. The core bridge applies
M11/M12/M13/M33; selected M31/M32/M36 operations also reside in the setup.
The historical M31/M36/M43 fields are not direct theorem applications. -/
structure M48Predecessors : Prop where
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m31 : RepairedSingularRegularLimitTheory.{u}
  m32 : RepairedHornSelectionTheory.{u}
  m33 : RepairedBranchContinuationTheory.{u}
  m36 : RepairedMetricSurgeryTheory.{u}
  m43 : RepairedUnifiedContinuationTheory.{u}

structure RepairedEpochExtensionTheory : Prop where
  one_step : M48Predecessors.{u} →
    ∀ S : RepairedControlledSchedulesData.{u},
    M48AnalyticCalibration S →
    ∀ N : RepairedNoncollapseInductionData.{u} S,
      ∀ C : RepairedCanonicalInductionData S N,
        Nonempty (RepairedEpochExtensionData S N C)

end PoincareMT
