import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinGraph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_exists_straight_join_graph_neighborhood
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {a A B b c : ℝ} (haA : a < A) (hBb : B < b) (hc : 0 < c)
    (hai : InjOn alpha (Icc a A)) (hbi : InjOn beta (Icc B b))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    {K : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ)
      (X : Set ℝ) (W : Set AnnulusCoordinates),
      (∀ z, L z = (inner ℝ (deriv alpha A) z,
        inner ℝ (quarterTurn (deriv alpha A)) z)) ∧
      IsOpen X ∧ ContinuousOn h X ∧ HasDerivAt h 0 (L (alpha A)).1 ∧
      IsOpen W ∧ alpha A ∈ W ∧
      ∀ z ∈ W, (L z).1 ∈ X ∧
        (z ∈ (alpha '' Icc a A ∪ beta '' Icc B b) ∪ K ↔ (L z).2 = h (L z).1) := by
  obtain ⟨epsilon, hepsilon, hebound, L, X, h, hL, hX, hh, hpX, hd, hgraph⟩ :=
    m64Intrinsic_exists_straight_join_graph ha hb
      (lt_min (sub_pos.mpr haA) (sub_pos.mpr hBb)) hc hend hreg htan
  have hea : epsilon < A - a := hebound.trans_le (min_le_left _ _)
  have heb : epsilon < b - B := hebound.trans_le (min_le_right _ _)
  let C := alpha '' Icc a (A - epsilon)
  let D := beta '' Icc (B + epsilon) b
  have hC : IsCompact C := isCompact_Icc.image ha.continuous
  have hD : IsCompact D := isCompact_Icc.image hb.continuous
  have hpC : alpha A ∉ C := by
    rintro ⟨t, ht, hpoint⟩
    have htA := hai ⟨ht.1, by linarith [ht.2]⟩ (right_mem_Icc.mpr haA.le) hpoint
    linarith [ht.2]
  have hpD : alpha A ∉ D := by
    rintro ⟨t, ht, hpoint⟩
    have htB := hbi ⟨by linarith [ht.1], ht.2⟩ (left_mem_Icc.mpr hBb.le)
      (hpoint.trans hend)
    linarith [ht.1]
  let W := (fun z : AnnulusCoordinates => (L z).1) ⁻¹' X ∩ (C ∪ D ∪ K)ᶜ
  have hW : IsOpen W := (hX.preimage L.continuous.fst).inter
    ((hC.union hD).union hK).isClosed.isOpen_compl
  have hpW : alpha A ∈ W := ⟨hpX, by
    rintro ((h | h) | h)
    · exact hpC h
    · exact hpD h
    · exact hpK h⟩
  refine ⟨L, h, X, W, hL, hX, hh, hd, hW, hpW, ?_⟩
  intro z hz
  refine ⟨hz.1, ?_⟩
  constructor
  · intro htrace
    apply (hgraph z hz.1).mp
    rcases htrace with (⟨t, ht, htz⟩ | ⟨t, ht, htz⟩) | hzK
    · have htlo : A - epsilon ≤ t := by
        by_contra hn
        exact hz.2 (Or.inl (Or.inl ⟨t, ⟨ht.1, (lt_of_not_ge hn).le⟩, htz⟩))
      exact Or.inl ⟨t, ⟨htlo, ht.2⟩, htz⟩
    · have hthi : t ≤ B + epsilon := by
        by_contra hn
        exact hz.2 (Or.inl (Or.inr ⟨t, ⟨(lt_of_not_ge hn).le, ht.2⟩, htz⟩))
      exact Or.inr ⟨t, ⟨ht.1, hthi⟩, htz⟩
    · exact False.elim (hz.2 (Or.inr hzK))
  · intro htrace
    rcases (hgraph z hz.1).mpr htrace with ⟨t, ht, htz⟩ | ⟨t, ht, htz⟩
    · exact Or.inl (Or.inl ⟨t, ⟨by linarith [ht.1], ht.2⟩, htz⟩)
    · exact Or.inl (Or.inr ⟨t, ⟨ht.1, by linarith [ht.2]⟩, htz⟩)

end PoincareConjecture
