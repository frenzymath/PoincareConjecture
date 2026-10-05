import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Nonround
import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Zero

/-! # Universal noncollapsing and zero asymptotic volume

The original M22 theorem at Mapher revision
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`, proved from its unchanged applied
predecessor services. The positive constant is constructed before any ancient
solution is chosen. All-dimensional volume decay uses the bounded-ancient
volume theorem through the exact calibrated-ratio bridge.
Reference: Morgan--Tian, Corollary 9.44, pp. 208--209, Proposition 9.58,
pp. 220--221, and Theorem 9.59, pp. 222--225.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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

end PoincareMT
