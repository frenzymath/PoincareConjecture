/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/GaugeRecovery.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Basic

/-!
# Gauge recovery certificate

This file records the small algebraic boundary between a parabolic metric
producer and the intrinsic Ricci equation.  The producer supplies the
derivative of its transported metric and a separately checked cancellation of
the gauge term.  The conversion below only rewrites that cancellation; it
does not assume a Ricci-flow object or a solver as data.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

namespace GaugeRecovery

/--
A transported metric family together with the two identities used in the
DeTurck gauge argument.  `source` is the equation before gauge cancellation;
`gaugeCorrection` is the Lie-derivative contribution.  The cancellation is
quantified over every compatible connection because the public short-time
contract is quantified that way as well.
-/
structure Certificate (g0 : RiemannianMetric n M) where
  T : ℝ
  hT : 0 < T
  metric : ℝ → RiemannianMetric n M
  connection : ∀ t : ℝ, LeviCivitaData (metric t)
  smooth : RiemannianMetric.IsSmoothFamilyOn metric (Set.Ico 0 T)
  initial : metric 0 = g0
  source : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  gaugeCorrection : ∀ (t : ℝ) (x : M),
    TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ
  transportedEquation : ∀ (t : ℝ), t ∈ Set.Ico 0 T →
    ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (metric s).inner x u v)
        (source t x u v - gaugeCorrection t x u v) (Set.Ico 0 T) t
  cancellation : ∀ (t : ℝ), t ∈ Set.Ico 0 T →
    ∀ (D : LeviCivitaData (metric t)) (x : M)
      (u v : TangentSpace (𝓡 n) x),
      source t x u v - gaugeCorrection t x u v = -2 * D.ricci x u v

/-- The transported equation after the gauge term has been cancelled. -/
theorem Certificate.equation
    {g0 : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g0)
    (t : ℝ) (ht : t ∈ Set.Ico 0 C.T)
    (D : LeviCivitaData (C.metric t)) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (C.metric s).inner x u v)
      (-2 * D.ricci x u v) (Set.Ico 0 C.T) t := by
  rw [← C.cancellation t ht D x u v]
  exact C.transportedEquation t ht x u v

/-- Forget the certificate's analytic bookkeeping and expose its metric
family in the exact telescope of `exists_ricciFlow_metricFamily`. -/
theorem Certificate.exists_metricFamily
    {g0 : RiemannianMetric n M} (C : Certificate (n := n) (M := M) g0) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D.ricci x u v) (Set.Ico 0 T) t := by
  refine ⟨C.T, C.hT, C.metric, C.initial, C.smooth, ?_⟩
  intro t ht D x u v
  exact C.equation t ht D x u v

end GaugeRecovery

end PoincareMT
