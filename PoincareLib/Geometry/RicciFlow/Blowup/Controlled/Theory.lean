import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
Adapted from Mapher `PoincareMT/Statements/M30ControlledBlowupLimits.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M30 controlled generalized-flow limit statement

Morgan--Tian Theorems 11.1 and 11.8 (pp. 267--279), with Corollaries 11.3--11.4
(pp. 269--270), are stated on primitive
generalized blowup sequences, base balls, canonical neighborhoods,
noncollapse, maximal flow-line survival, and guarded absolute analytic bounds.
M30 selects one universal epsilon threshold using the actual M29 service,
including its applications at earlier basepoints. The theorem keeps finite and infinite
horizon conclusions separate and does not require a fixed-carrier coercion.

The short conclusion is a geometric limit on some positive backward interval;
the long conclusion is a limit on every finite slab below T₀, with
scale-bounded noncollapse. At T₀ = infinity, it additionally identifies an
actual ancient kappa-solution with the same limit flow and connection.
The finite-scale formulation records the corrected compactness/noncollapse
interfaces associated with MT-COMPACTNESS-5.15 and MT-NONCOLLAPSING-VARIANTS.

The supporting geometric branch uses actual bounded cylinders and a terminal
volume lower bound directly. It gives no kappa-identification. Its spatially
uniform slab bounds address the Theorem 5.15 correction, and its past buffer
gives the same time-zero jet convergence as the other branches. See
`reviews/contracts/2026-09-15-geometric-compactness-round1.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedShortControlledBlowupConclusion
    (S : GeneralizedBlowupSequence.{u}) where
  backward_time : ℝ
  backward_time_pos : 0 < backward_time
  convergence : Nonempty (GeneralizedBlowupConvergence S
    (Set.Icc (-backward_time) 0))

structure RepairedLongControlledBlowupConclusion
    (S : GeneralizedBlowupSequence.{u})
    (kappa r₀ : ℝ) (T₀ : ℝ≥0∞) where
  convergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)
  noncollapsed : M30LimitNoncollapsedAtScale convergence.limit kappa r₀
  ancient : ∀ h : T₀ = ⊤,
    Nonempty (M30AncientKappaIdentification (h ▸ convergence.limit) kappa)

def M30ShortLimitStatement (epsilon₀ : ℝ) : Prop :=
  ∀ (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ),
    epsilon ≤ epsilon₀ →
    M30CommonBlowupControls S epsilon C kappa r₀ mu →
    Nonempty (RepairedShortControlledBlowupConclusion S)

def M30LongLimitStatement (epsilon₀ : ℝ) : Prop :=
  ∀ (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ) (T₀ : ℝ≥0∞),
    epsilon ≤ epsilon₀ →
    M30LongBlowupControls S epsilon C kappa r₀ mu T₀ →
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀)

structure RepairedControlledBlowupLimitTheory : Prop where
  geometric_long : ∀ (S : GeneralizedBlowupSequence.{u}) (T₀ : ℝ≥0∞),
    M30GeometricLongControls S T₀ →
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
  limits : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
    M30ShortLimitStatement.{u} epsilon₀ ∧ M30LongLimitStatement.{u} epsilon₀

end PoincareMT
