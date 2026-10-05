import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.Sequence
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Reindexing the actual generalized blowup sequence

Morgan--Tian Claim 11.32, printed pp. 287-288, uses terminal extensions
with varying carriers and original terminal times. The continuation after
Claim 11.35, p. 291, passes to subsequences. Reindexing retains those flows,
their dependent bases, and every primitive common compactness control.

The bounded derivation is `claim11_32-sequence-reindex.md`. These are direct
constructions from the frozen records, not an assumption of geometric
continuation or of any identification between subsequential limits.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

section Reindex

variable (S : GeneralizedBlowupSequence.{u}) (phi : ℕ → ℕ) (hphi : StrictMono phi)

/-- Select the original generalized flows and their actual dependent bases;
this is the subsequence operation used after Claim 11.35, printed p. 291. -/
def blowupSequenceComp : GeneralizedBlowupSequence.{u} where
  flow k := S.flow (phi k)
  base k := S.base (phi k)
  base_scalar_pos k := S.base_scalar_pos (phi k)
  scalar_diverges := S.scalar_diverges.comp hphi.tendsto_atTop

/-- Reindexing retains the selected original flow, as in the continuation
after Claim 11.35, printed p. 291. -/
@[simp] theorem blowupSequenceComp_flow (k : ℕ) :
    (blowupSequenceComp S phi hphi).flow k = S.flow (phi k) := rfl

/-- Reindexing retains the original spacetime base, including its clock;
the subsequence argument follows Claim 11.35, printed p. 291. -/
@[simp] theorem blowupSequenceComp_base (k : ℕ) :
    (blowupSequenceComp S phi hphi).base k = S.base (phi k) := rfl

/-- The selected scalar normalization is unchanged in the subsequence
argument after Claim 11.35, printed p. 291. -/
@[simp] theorem blowupSequenceComp_scale (k : ℕ) :
    (blowupSequenceComp S phi hphi).scale k = S.scale (phi k) := rfl

/-- Every normalized base ball is the same set in the selected original
slice, as used after Claim 11.35, printed p. 291. -/
@[simp] theorem blowupSequenceComp_baseBall (k : ℕ) (A : ℝ) :
    (blowupSequenceComp S phi hphi).baseBall k A = S.baseBall (phi k) A := rfl

/-- A further subsequence composes the index maps in their original order;
this is the repeated extraction after Claim 11.35, printed p. 291. -/
theorem blowupSequenceComp_comp (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    blowupSequenceComp (blowupSequenceComp S phi hphi) psi hpsi =
      blowupSequenceComp S (phi ∘ psi) (hphi.comp hpsi) := rfl

/-- All primitive common controls survive a strict reindexing with the
same constants, as required after Claim 11.35, printed p. 291. -/
def blowupSequenceComp_commonControls {epsilon C kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon C kappa r₀ mu) :
    M30CommonBlowupControls (blowupSequenceComp S phi hphi) epsilon C kappa r₀ mu where
  epsilon_pos := H.epsilon_pos
  C_pos := H.C_pos
  kappa_pos := H.kappa_pos
  radius_pos := H.radius_pos
  branch k := H.branch (phi k)
  canonical k := H.canonical (phi k)
  analytic_constant := H.analytic_constant
  analytic_constant_pos := H.analytic_constant_pos
  scalar_gradient_bound k := H.scalar_gradient_bound (phi k)
  scalar_time_derivative_bound k := H.scalar_time_derivative_bound (phi k)
  balls_compact A hA := hphi.tendsto_atTop.eventually (H.balls_compact A hA)
  noncollapsed_at_zero A hA := hphi.tendsto_atTop.eventually (H.noncollapsed_at_zero A hA)
  mu_pos := H.mu_pos
  maximal_worldlines A hA := hphi.tendsto_atTop.eventually (H.maximal_worldlines A hA)

end Reindex

section Terminal

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

/-- Reindexing the terminal sequence equals selecting the original family
first, retaining its varying carriers and clocks; Claims 11.32/11.35,
printed pp. 287-288 and 291. -/
theorem terminalBlowupSequence_comp (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    blowupSequenceComp (terminalBlowupSequence H Q x hpos hdiv) phi hphi =
      terminalBlowupSequence (M := fun k => M (phi k))
        (F := fun k => F (phi k)) (T := fun k => T (phi k))
        (fun k => H (phi k)) (fun k => Q (phi k)) (fun k => x (phi k))
        (fun k => hpos (phi k)) (hdiv.comp hphi.tendsto_atTop) := rfl

end Terminal

end PoincareMT.M32
