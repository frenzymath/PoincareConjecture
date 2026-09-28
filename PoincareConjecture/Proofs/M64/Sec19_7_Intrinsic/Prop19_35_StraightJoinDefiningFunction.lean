import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuousGraphDefiningFunction

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_exists_straight_join_defining_function
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a A B b c : ℝ} (haA : a < A) (hBb : B < b) (hc : 0 < c)
    (hai : InjOn alpha (Icc a A)) (hbi : InjOn beta (Icc B b))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = (alpha '' Icc a A ∪ beta '' Icc B b) ∪ K)
    (hfV : frontier V = frontier U) :
    ∃ (phi : AnnulusCoordinates → ℝ) (ell : AnnulusCoordinates →L[ℝ] ℝ),
      HasFDerivAt phi ell (alpha A) ∧ phi (alpha A) = 0 ∧ ell ≠ 0 ∧
        (∀ᶠ z in 𝓝 (alpha A), z ∈ closure U ↔ 0 ≤ phi z) := by
  obtain ⟨L, h, X, W, _, hX, hh, hd, hW, hpW, hgraph⟩ :=
    m64Intrinsic_exists_straight_join_graph_neighborhood ha hb haA hBb hc hai hbi
      hend hreg htan hK hpK
  apply m64Intrinsic_continuous_graph_defining_function L hX hh hd
    hU hV hdisj hfV hW hpW
  · rw [hfU]
    exact Or.inl (Or.inl ⟨A, right_mem_Icc.mpr haA.le, rfl⟩)
  · intro z hz
    rw [hfU]
    exact hgraph z hz

end PoincareConjecture
