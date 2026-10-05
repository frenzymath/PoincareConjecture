import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Straight.JoinNeighborhood
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Continuous.GraphRelativeCover

/-! Relative coverage at the actual regular straight join of two smooth arcs.

Morgan--Tian context: Claim 19.40, printed pp. 470-471, within Proposition 19.35,
pp. 467-481. These project constructions supply the actual collar and straight-join
geometry for the regional Gauss--Bonnet argument.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareMT

/-- The actual joined arcs construct the continuous graph needed for relative coverage. The
fitted set's local frontier is the only remaining input; no smooth extension through the
joined curve is assumed. Source:
`proof-work/tasks/M64/derivations/2026-09-27-minimal-contact-regularity.md`, Section 12. -/
theorem m64Intrinsic_exists_straight_join_relative_cover
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a A B b c : ℝ} (haA : a < A) (hBb : B < b) (hc : 0 < c)
    (hai : InjOn alpha (Icc a A)) (hbi : InjOn beta (Icc B b))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    {D U V : Set AnnulusCoordinates} (hD : IsCompact D) (hpD : alpha A ∉ D)
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hfU : frontier U = (alpha '' Icc a A ∪ beta '' Icc B b) ∪ D)
    (hfV : frontier V = frontier U)
    {K : Set AnnulusCoordinates} (hK : IsClosed K)
    (hKregular : closure (interior K) = K) (hKsub : K ⊆ closure U)
    (hpK : alpha A ∈ K) {N : Set AnnulusCoordinates} (hN : N ∈ 𝓝 (alpha A))
    (hfrontK : N ∩ frontier K ⊆ frontier U) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ alpha A ∈ W ∧ W ∩ closure U ⊆ K := by
  obtain ⟨L, h, X, W, _, hX, hh, _, hW, hpW, hgraph⟩ :=
    m64Intrinsic_exists_straight_join_graph_neighborhood ha hb haA hBb hc hai hbi
      hend hreg htan hD hpD
  have hpfront : alpha A ∈ frontier U := by
    rw [hfU]
    exact Or.inl (Or.inl (mem_image_of_mem alpha (right_mem_Icc.mpr haA.le)))
  apply m64Intrinsic_exists_continuous_graph_relative_cover L hX hh hU hV hd hfV
    hW hpW hpfront _ hK hKregular hKsub hpK hN hfrontK
  intro z hz
  simpa only [hfU] using hgraph z hz

end PoincareMT
