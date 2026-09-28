import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem IsFinitePLBallPair.mapsTo_nonpos_of_zeros_in_boundary
    {d q : Set X} (hd : IsFinitePLBallPair E d q)
    (f : X → ℝ) (hf : ContinuousOn f d)
    (hzero : d ∩ {x | f x = 0} ⊆ q)
    (hneg : ∃ x ∈ d, f x < 0) : MapsTo f d (Iic 0) := by
  have hnonzero : ∀ x ∈ d \ q, f x ≠ 0 :=
    fun x hx hz => hx.2 (hzero ⟨hx.1, hz⟩)
  have hfc : ContinuousOn f (closure (d \ q)) := by
    rw [hd.closure_sdiff]
    exact hf
  rcases hd.isConnected_sdiff.isPreconnected.mapsTo_Ioi_or_Iio
      (hf.mono sdiff_subset) hnonzero with hpos | hnegative
  · have hweak := hpos.closure_of_continuousOn hfc
    rw [hd.closure_sdiff, closure_Ioi] at hweak
    obtain ⟨x, hx, hfx⟩ := hneg
    exact (not_lt_of_ge (hweak hx) hfx).elim
  · have hweak := hnegative.closure_of_continuousOn hfc
    rwa [hd.closure_sdiff, closure_Iio] at hweak

theorem IsFinitePLBallPair.mapsTo_nonneg_of_zeros_in_boundary
    {d q : Set X} (hd : IsFinitePLBallPair E d q)
    (f : X → ℝ) (hf : ContinuousOn f d)
    (hzero : d ∩ {x | f x = 0} ⊆ q)
    (hpos : ∃ x ∈ d, 0 < f x) : MapsTo f d (Ici 0) := by
  have hneg : ∃ x ∈ d, -f x < 0 := by
    obtain ⟨x, hx, hfx⟩ := hpos
    exact ⟨x, hx, neg_neg_of_pos hfx⟩
  have hzero' : d ∩ {x | -f x = 0} ⊆ q :=
    fun x hx => hzero ⟨hx.1, neg_eq_zero.mp hx.2⟩
  have h := hd.mapsTo_nonpos_of_zeros_in_boundary (fun x => -f x)
    hf.neg hzero' hneg
  intro x hx
  change 0 ≤ f x
  exact neg_nonpos.mp (show -f x ≤ 0 from h hx)

variable [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.isFinitePLBallPair_signed_halves_of_zero_arc
    {s q W : Set X} {a b : X}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (f : X → ℝ) (hf : ContinuousOn f s)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hWzero : s ∩ {x | f x = 0} = W)
    (hqzero : q ∩ {x | f x = 0} = {a, b})
    (hU : IsFinitePLBallPair ℝ (q ∩ {x | f x ≤ 0}) {a, b})
    (hV : IsFinitePLBallPair ℝ (q ∩ {x | 0 ≤ f x}) {a, b})
    (hneg : ∃ x ∈ q, f x < 0) (hpos : ∃ x ∈ q, 0 < f x) :
    IsFinitePLBallPair (ℝ × ℝ) (s ∩ {x | f x ≤ 0})
        ((q ∩ {x | f x ≤ 0}) ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) (s ∩ {x | 0 ≤ f x})
        (W ∪ (q ∩ {x | 0 ≤ f x})) := by
  let U := q ∩ {x | f x ≤ 0}
  let V := q ∩ {x | 0 ≤ f x}
  have hUV : U ∩ V ⊆ ({a, b} : Set X) :=
    fun x hx => hqzero.subset ⟨hx.1.1, le_antisymm hx.1.2 hx.2.2⟩
  have hrim : U ∪ V = q := by
    ext x
    constructor
    · exact fun hx => hx.elim And.left And.left
    · intro hx
      exact (le_total (f x) 0).elim
        (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hproper : W \ {a, b} ⊆ s \ q := by
    intro x hx
    have hz := hWzero.symm.subset hx.1
    exact ⟨hz.1, fun hxq => hx.2 (hqzero.subset ⟨hxq, hz.2⟩)⟩
  obtain ⟨d₀, d₁, hd₀, hd₁, hwhole, hcommon, _, _⟩ :=
    hs.exists_proper_arc_cut hU hV hW hab hUV hrim hproper
  have hd₀s : d₀ ⊆ s := subset_union_left.trans hwhole.subset
  have hd₁s : d₁ ⊆ s := subset_union_right.trans hwhole.subset
  have hnonpos : MapsTo f d₀ (Iic 0) := by
    apply hd₀.mapsTo_nonpos_of_zeros_in_boundary f (hf.mono hd₀s)
    · exact fun x hx => Or.inr (hWzero.subset ⟨hd₀s hx.1, hx.2⟩)
    · obtain ⟨x, hxq, hfx⟩ := hneg
      exact ⟨x, hd₀.1 (Or.inl ⟨hxq, hfx.le⟩), hfx⟩
  have hnonneg : MapsTo f d₁ (Ici 0) := by
    apply hd₁.mapsTo_nonneg_of_zeros_in_boundary f (hf.mono hd₁s)
    · exact fun x hx => Or.inl (hWzero.subset ⟨hd₁s hx.1, hx.2⟩)
    · obtain ⟨x, hxq, hfx⟩ := hpos
      exact ⟨x, hd₁.1 (Or.inr ⟨hxq, hfx.le⟩), hfx⟩
  have hd₀eq : d₀ = s ∩ {x | f x ≤ 0} := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hd₀s hx, hnonpos hx⟩
    intro x hx
    rcases hwhole.symm.subset hx.1 with hx₀ | hx₁
    · exact hx₀
    · have hfx : f x = 0 := le_antisymm hx.2 (show 0 ≤ f x from hnonneg hx₁)
      have hxW : x ∈ W := hWzero.subset ⟨hx.1, hfx⟩
      exact (hcommon.symm.subset hxW).1
  have hd₁eq : d₁ = s ∩ {x | 0 ≤ f x} := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hd₁s hx, hnonneg hx⟩
    intro x hx
    rcases hwhole.symm.subset hx.1 with hx₀ | hx₁
    · have hfx : f x = 0 := le_antisymm (show f x ≤ 0 from hnonpos hx₀) hx.2
      have hxW : x ∈ W := hWzero.subset ⟨hx.1, hfx⟩
      exact (hcommon.symm.subset hxW).2
    · exact hx₁
  exact ⟨hd₀eq ▸ hd₀, hd₁eq ▸ hd₁⟩

theorem IsFinitePLBallPair.signed_halves_of_zero_arc
    {s q W : Set X} {a b : X}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (f : X → ℝ) (hf : ContinuousOn f s)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hWzero : s ∩ {x | f x = 0} = W)
    (hqzero : q ∩ {x | f x = 0} = {a, b})
    (hneg : ∃ x ∈ q, f x < 0) (hpos : ∃ x ∈ q, 0 < f x) :
    IsFinitePLBallPair (ℝ × ℝ) (s ∩ {x | f x ≤ 0})
        ((q ∩ {x | f x ≤ 0}) ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) (s ∩ {x | 0 ≤ f x})
        (W ∪ (q ∩ {x | 0 ≤ f x})) := by
  have ha : a ∈ q := (hqzero.symm.subset (by simp)).1
  have hb : b ∈ q := (hqzero.symm.subset (by simp)).1
  obtain ⟨U, V, hU, hV, hUV, _⟩ := hs.exists_boundary_arcs ha hb hab
  have harcs := isFinitePLBallPair_signed_halves_of_arcs hU hV hUV f
    (hf.mono hs.1) hqzero hneg hpos
  exact hs.isFinitePLBallPair_signed_halves_of_zero_arc f hf hW hab hWzero
    hqzero harcs.1 harcs.2 hneg hpos

end Set
