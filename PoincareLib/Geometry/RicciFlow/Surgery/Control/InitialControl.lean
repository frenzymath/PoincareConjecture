import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
Adapted from Mapher `PoincareMT/Definitions/M45InitialControl.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M45 initial control on raw surgery flows

Claim 15.1 and the discussion before Definition 15.7, pp. 353 and 360,
apply to the actual initial metric. The conclusion controls only times
in the supplied flow's domain, which may have an included regular endpoint.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Initial curvature and full volume estimates on every actual raw flow.
The scalar coefficient 18 is the elementary bound `|R| <= 9 |Rm|` in
dimension three. No later canonical or analytic control is a premise. -/
def M45InitialSurgeryControl (epsilon kappa0 : ℝ) : Prop :=
  ∀ F : SurgeryFlowData.{u},
    Disjoint F.surgery_times (Set.Icc 0 (1 / 16 : ℝ)) ∧
      ∀ t ∈ F.time_domain, t ≤ 1 / 16 → ∀ x : (F.slice t).carrier,
        (F.connection t).curvatureTensorNorm x ≤ 2 ∧
        |(F.connection t).scalarCurvature x| ≤ 18 ∧
        ∀ r : ℝ, 0 < r → r ≤ epsilon →
          ENNReal.ofReal (kappa0 * r ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)

end PoincareMT
