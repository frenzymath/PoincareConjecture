import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Zero











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m22UniversalNoncollapsingAndZeroAVR (n : ℕ)
    (P : M22UniversalNoncollapsingPredecessors.{u} n) :
    Nonempty (UniversalNoncollapsingConclusion.{u} n) := by
  classical
  refine ⟨{
    data := universalNoncollapseData P.noncollapse_generalized
    three_dimensional_alternative := ?_
    nonround_is_universally_noncollapsed := ?_
    asymptotic_volume_ratio_zero := ?_ }⟩
  · intro M _ _ _ _ _ _ _ _ _ K
    by_cases hround : IsRoundAncientKappaSolution K
    · exact Or.inl hround
    · exact Or.inr (P.nonround_is_universally_noncollapsed K hround)
  · intro M _ _ _ _ _ _ _ _ _ K hK
    exact P.nonround_is_universally_noncollapsed K hK
  · intro M _ _ _ _ _ _ _ _ _ K
    exact P.asymptotic_volume_ratio_zero K

theorem m22UniversalNoncollapsingConclusionTheory (n : ℕ)
    (P : M22UniversalNoncollapsingPredecessors.{u} n) :
    Nonempty (UniversalNoncollapsingConclusion.{u} n) :=
  m22UniversalNoncollapsingAndZeroAVR n P

end PoincareConjecture
