import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def generalizedSliceStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u}) (epsilon C Q s : ℝ) : Prop :=
  ∀ y : (F.slice s).carrier, Q ≤ F.scalar ⟨s, y⟩ →
    Nonempty (GeneralizedCanonicalControl (F := F) s y epsilon C)

def generalizedEarlierStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u})
    (epsilon C t : ℝ) (x : (F.slice t).carrier) : Prop :=
  ∀ s, s ∈ F.interval → s ≤ t →
    ∀ y : (F.slice s).carrier,
      4 * F.scalar ⟨t, x⟩ ≤ F.scalar ⟨s, y⟩ →
        Nonempty (GeneralizedCanonicalControl (F := F) s y epsilon C)

def generalizedEarlierDenseStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u})
    (epsilon C t : ℝ) (x : (F.slice t).carrier) : Prop :=
  ∀ s, s ∈ F.interval → s ≤ t → ∀ a, a < s →
    ∃ u, u ∈ F.interval ∧ a < u ∧ u ≤ s ∧
      generalizedSliceStrongCanonicalNeighborhoods F epsilon C
        (4 * F.scalar ⟨t, x⟩) u

theorem generalizedEarlierStrongCanonicalNeighborhoods.left_dense
    {F : GeneralizedRicciFlowData.{u}} {epsilon C t : ℝ}
    {x : (F.slice t).carrier}
    (h : generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x := by
  intro s hs hst a has
  exact ⟨s, hs, has, le_rfl, h s hs hst⟩

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

end PoincareConjecture
