import PoincareLib.Geometry.RicciFlow.Generalized.CanonicalNeighborhood

/-!
# Uniform bounded-distance estimates for generalized flows

Adapted without changing declaration bodies from Mapher commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Morgan--Tian, Theorem 10.2, pp. 245--246, and the opening of the proof of
Theorem 11.1, p. 269. The uniform estimate remains an explicit premise.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

def generalizedEarlierStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u})
    (epsilon C t : ℝ) (x : (F.slice t).carrier) : Prop :=
  ∀ s, s ∈ F.interval → s ≤ t →
    ∀ y : (F.slice s).carrier,
      4 * F.scalar ⟨t, x⟩ ≤ F.scalar ⟨s, y⟩ →
        Nonempty (GeneralizedCanonicalControl (F := F) s y epsilon C)

def generalizedHamiltonIveyPinchedAt
    (F : GeneralizedRicciFlowData.{u}) (t : ℝ) : Prop :=
  t ∈ F.interval ∧ 0 ≤ t ∧
    (∀ x : (F.slice t).carrier,
      -6 / (1 + 4 * t) ≤ F.scalar ⟨t, x⟩) ∧
    (∀ x : (F.slice t).carrier,
      0 < (F.connection t).negativeCurvaturePart x →
        F.scalar ⟨t, x⟩ ≥
          2 * (F.connection t).negativeCurvaturePart x *
            (Real.log ((F.connection t).negativeCurvaturePart x) +
              Real.log (1 + t) - 3))

def generalizedHamiltonIveyPinched
    (F : GeneralizedRicciFlowData.{u}) : Prop :=
  ∀ t, t ∈ F.interval → generalizedHamiltonIveyPinchedAt F t

def generalizedWeakHamiltonIveyPinched
    (F : GeneralizedRicciFlowData.{u}) : Prop :=
  ∀ t ∈ F.interval, ∀ x : (F.slice t).carrier,
    -6 ≤ F.scalar ⟨t, x⟩ ∧
      (0 < (F.connection t).negativeCurvaturePart x →
        F.scalar ⟨t, x⟩ ≥
          2 * (F.connection t).negativeCurvaturePart x *
            (Real.log ((F.connection t).negativeCurvaturePart x) - 3))

/-- Discarding the nonnegative absolute clock gives equation (10.1) of
Morgan--Tian, printed p. 247. -/
theorem generalizedHamiltonIveyPinched.weak
    {F : GeneralizedRicciFlowData.{u}} (h : generalizedHamiltonIveyPinched F) :
    generalizedWeakHamiltonIveyPinched F := by
  intro t ht x
  obtain ⟨_, ht0, hscalar, hpinch⟩ := h t ht
  constructor
  · have hden : 0 < 1 + 4 * t := by positivity
    have hlower : (-6 : ℝ) ≤ -6 / (1 + 4 * t) :=
      (le_div_iff₀ hden).mpr (by nlinarith)
    exact hlower.trans (hscalar x)
  · intro hv
    have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    have hmul := mul_nonneg (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hv)) hlog
    have hfull := hpinch x hv
    nlinarith

def generalizedNonnegativeCurvature
    (F : GeneralizedRicciFlowData.{u}) : Prop :=
  (∀ t ∈ F.interval, ∀ x : (F.slice t).carrier,
      0 ≤ F.scalar ⟨t, x⟩ ∧
        (F.connection t).negativeCurvaturePart x = 0) ∧
  generalizedWeakHamiltonIveyPinched F

def generalizedPinchedOrNonnegative
    (F : GeneralizedRicciFlowData.{u}) : Prop :=
  (F.interval ⊆ Set.Ici 0 ∧ generalizedHamiltonIveyPinched F) ∨
    generalizedNonnegativeCurvature F

/-- A nonnegative-curvature flow on a nonnegative time interval also satisfies
the normalized Hamilton--Ivey predicate used by the bounded-distance service.
The time normalization is proved at this adapter boundary; it is not part of
`generalizedNonnegativeCurvature` itself. -/
theorem generalizedHamiltonIveyPinched_of_nonnegative
    {F : GeneralizedRicciFlowData.{u}}
    (hinterval : F.interval ⊆ Set.Ici 0)
    (hnonnegative : generalizedNonnegativeCurvature F) :
    generalizedHamiltonIveyPinched F := by
  intro t ht
  have ht0 : 0 ≤ t := hinterval ht
  refine ⟨ht, ht0, ?_, ?_⟩
  · intro x
    exact le_trans (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith))
      (hnonnegative.1 t ht x).1
  · intro x hx
    rw [(hnonnegative.1 t ht x).2] at hx
    exact (lt_irrefl 0 hx).elim

def RepairedBoundedDistanceEstimate
    (F : GeneralizedRicciFlowData.{u}) (A D t : ℝ)
    (x : (F.slice t).carrier) : Prop :=
  ∀ y : (F.slice t).carrier,
    y ∈ (F.metric t).ball x
      (A * F.scalar ⟨t, x⟩ ^ (-1 / 2 : ℝ)) →
      F.scalar ⟨t, y⟩ ≤ D * F.scalar ⟨t, x⟩

structure RepairedBoundedDistanceTheory : Prop where
  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          generalizedWeakHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x

end PoincareMT
