import PoincareConjecture.Proofs.M32.Claim11_32.Sequence
import PoincareConjecture.Definitions.M30ControlledBlowupLimits
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

section Reindex

variable (S : GeneralizedBlowupSequence.{u}) (phi : ℕ → ℕ) (hphi : StrictMono phi)

def blowupSequenceComp : GeneralizedBlowupSequence.{u} where
  flow k := S.flow (phi k)
  base k := S.base (phi k)
  base_scalar_pos k := S.base_scalar_pos (phi k)
  scalar_diverges := S.scalar_diverges.comp hphi.tendsto_atTop

@[simp] theorem blowupSequenceComp_flow (k : ℕ) :
    (blowupSequenceComp S phi hphi).flow k = S.flow (phi k) := rfl

@[simp] theorem blowupSequenceComp_base (k : ℕ) :
    (blowupSequenceComp S phi hphi).base k = S.base (phi k) := rfl

@[simp] theorem blowupSequenceComp_scale (k : ℕ) :
    (blowupSequenceComp S phi hphi).scale k = S.scale (phi k) := rfl

@[simp] theorem blowupSequenceComp_baseBall (k : ℕ) (A : ℝ) :
    (blowupSequenceComp S phi hphi).baseBall k A = S.baseBall (phi k) A := rfl

theorem blowupSequenceComp_comp (psi : ℕ → ℕ) (hpsi : StrictMono psi) :
    blowupSequenceComp (blowupSequenceComp S phi hphi) psi hpsi =
      blowupSequenceComp S (phi ∘ psi) (hphi.comp hpsi) := rfl

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

theorem terminalBlowupSequence_comp (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    blowupSequenceComp (terminalBlowupSequence H Q x hpos hdiv) phi hphi =
      terminalBlowupSequence (M := fun k => M (phi k))
        (F := fun k => F (phi k)) (T := fun k => T (phi k))
        (fun k => H (phi k)) (fun k => Q (phi k)) (fun k => x (phi k))
        (fun k => hpos (phi k)) (hdiv.comp hphi.tendsto_atTop) := rfl

end Terminal

end PoincareConjecture.M32
