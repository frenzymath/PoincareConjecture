import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_convex_frontier_four_regions (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hspace : K.space = C) (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hq : q ∈ interior C) (hqA : A q = 0)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPC : P.boundary ℝ ⊆ frontier C)
    {a b : E} (hab : a ≠ b)
    (hzero : P.boundary ℝ ∩ {x | A x = 0} = {a, b})
    (hneg : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    ∃ U V d₀₀ d₀₁ d₁₀ d₁₁ : Set E,
      IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = frontier C ∩ {x | A x = 0} ∧ U ∩ V = {a, b} ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀₀ (U ∪ (P.boundary ℝ ∩ {x | 0 ≤ A x})) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀₁ ((P.boundary ℝ ∩ {x | 0 ≤ A x}) ∪ V) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁₀ (U ∪ (P.boundary ℝ ∩ {x | A x ≤ 0})) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁₁ ((P.boundary ℝ ∩ {x | A x ≤ 0}) ∪ V) ∧
      d₀₀ ∪ d₀₁ = frontier C ∩ {x | 0 ≤ A x} ∧
      d₁₀ ∪ d₁₁ = frontier C ∩ {x | A x ≤ 0} ∧
      d₀₀ ∩ d₀₁ = P.boundary ℝ ∩ {x | 0 ≤ A x} ∧
      d₁₀ ∩ d₁₁ = P.boundary ℝ ∩ {x | A x ≤ 0} ∧
      d₀₀ ∩ (frontier C ∩ {x | A x = 0}) = U ∧
      d₀₁ ∩ (frontier C ∩ {x | A x = 0}) = V ∧
      d₁₀ ∩ (frontier C ∩ {x | A x = 0}) = U ∧
      d₁₁ ∩ (frontier C ∩ {x | A x = 0}) = V ∧
      d₀₀ ∩ d₁₀ = U ∧ d₀₁ ∩ d₁₁ = V ∧
      d₀₀ ∩ d₁₁ = {a, b} ∧ d₀₁ ∩ d₁₀ = {a, b} ∧
      (d₀₀ ∪ d₀₁) ∪ (d₁₀ ∪ d₁₁) = frontier C := by
  let R := frontier C ∩ {x | A x = 0}
  let Hpos := frontier C ∩ {x | 0 ≤ A x}
  let Hneg := frontier C ∩ {x | A x ≤ 0}
  let Wpos := P.boundary ℝ ∩ {x | 0 ≤ A x}
  let Wneg := P.boundary ℝ ∩ {x | A x ≤ 0}
  have hmid (x : E) : A (midpoint ℝ q x) = A x / 2 := by
    rw [A.map_midpoint, midpoint_eq_smul_add, hqA, zero_add]
    simp only [invOf_eq_inv, smul_eq_mul]
    ring
  have hmidint (x : E) (hx : x ∈ P.boundary ℝ) : midpoint ℝ q x ∈ interior C :=
    hcv.openSegment_interior_self_subset_interior hq
      (hC.isClosed.frontier_subset (hPC hx)) (midpoint_mem_openSegment q x)
  have hdim' : Module.finrank ℝ E = Module.finrank ℝ (ℝ × ℝ) + 1 := by
    simpa [Module.finrank_prod] using hdim
  have hnegative : ∃ x ∈ interior C, A x < 0 := by
    obtain ⟨x, hx, hxA⟩ := hneg
    exact ⟨midpoint ℝ q x, hmidint x hx, by rw [hmid]; linarith⟩
  have hpositive : ∃ x ∈ interior C, 0 < A x := by
    obtain ⟨x, hx, hxA⟩ := hpos
    exact ⟨midpoint ℝ q x, hmidint x hx, by rw [hmid]; linarith⟩
  have hHpos : IsFinitePLBallPair (ℝ × ℝ) Hpos R :=
    K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hspace A
      hnegative ⟨q, hq, hqA⟩ hdim'
  have hHneg : IsFinitePLBallPair (ℝ × ℝ) Hneg R := by
    have hn : ∃ x ∈ interior C, (-A) x < 0 := by
      obtain ⟨x, hx, hxA⟩ := hpositive
      exact ⟨x, hx, by change -A x < 0; exact neg_neg_of_pos hxA⟩
    have hz : ∃ x ∈ interior C, (-A) x = 0 :=
      ⟨q, hq, by change -A q = 0; rw [hqA, neg_zero]⟩
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_nonneg, neg_eq_zero] using
      K.isFinitePLBallPair_convex_frontier_affine_cap hK hC hcv hspace (-A) hn hz hdim'
  have ha : a ∈ R := by
    have ha' := hzero.symm.subset (show a ∈ ({a, b} : Set E) by simp)
    exact ⟨hPC ha'.1, ha'.2⟩
  have hb : b ∈ R := by
    have hb' := hzero.symm.subset (show b ∈ ({a, b} : Set E) by simp)
    exact ⟨hPC hb'.1, hb'.2⟩
  obtain ⟨U, V, hU, hV, hUV, hUVi⟩ := hHpos.exists_boundary_arcs ha hb hab
  obtain ⟨hWneg, hWpos⟩ := P.isFinitePLBallPair_signed_halves hP hinj A
    A.continuous_of_finiteDimensional.continuousOn hab hzero hneg hpos
  have hproperPos : Wpos \ {a, b} ⊆ Hpos \ R := by
    intro x hx
    refine ⟨⟨hPC hx.1.1, hx.1.2⟩, ?_⟩
    exact fun hr => hx.2 (hzero.subset ⟨hx.1.1, hr.2⟩)
  have hproperNeg : Wneg \ {a, b} ⊆ Hneg \ R := by
    intro x hx
    refine ⟨⟨hPC hx.1.1, hx.1.2⟩, ?_⟩
    exact fun hr => hx.2 (hzero.subset ⟨hx.1.1, hr.2⟩)
  obtain ⟨d₀₀, d₀₁, h₀₀, h₀₁, hposUnion, hposInter, h₀₀R, h₀₁R⟩ :=
    hHpos.exists_proper_arc_cut hU hV hWpos hab hUVi.subset hUV hproperPos
  obtain ⟨d₁₀, d₁₁, h₁₀, h₁₁, hnegUnion, hnegInter, h₁₀R, h₁₁R⟩ :=
    hHneg.exists_proper_arc_cut hU hV hWneg hab hUVi.subset hUV hproperNeg
  have h₀₀pos : d₀₀ ⊆ Hpos := subset_union_left.trans hposUnion.subset
  have h₀₁pos : d₀₁ ⊆ Hpos := subset_union_right.trans hposUnion.subset
  have h₁₀neg : d₁₀ ⊆ Hneg := subset_union_left.trans hnegUnion.subset
  have h₁₁neg : d₁₁ ⊆ Hneg := subset_union_right.trans hnegUnion.subset
  have hcross {D₀ D₁ U₀ U₁ : Set E} (hD₀ : D₀ ⊆ Hpos) (hD₁ : D₁ ⊆ Hneg)
      (hD₀R : D₀ ∩ R = U₀) (hD₁R : D₁ ∩ R = U₁) : D₀ ∩ D₁ = U₀ ∩ U₁ := by
    ext x
    constructor
    · intro hx
      have hxR : x ∈ R :=
        ⟨(hD₀ hx.1).1, le_antisymm (hD₁ hx.2).2 (hD₀ hx.1).2⟩
      exact ⟨hD₀R.subset ⟨hx.1, hxR⟩, hD₁R.subset ⟨hx.2, hxR⟩⟩
    · intro hx
      exact ⟨(hD₀R.symm.subset hx.1).1, (hD₁R.symm.subset hx.2).1⟩
  refine ⟨U, V, d₀₀, d₀₁, d₁₀, d₁₁, hU, hV, hUV, hUVi,
    h₀₀, h₀₁, h₁₀, h₁₁, hposUnion, hnegUnion, hposInter, hnegInter,
    h₀₀R, h₀₁R, h₁₀R, h₁₁R, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [inter_self] using hcross h₀₀pos h₁₀neg h₀₀R h₁₀R
  · simpa only [inter_self] using hcross h₀₁pos h₁₁neg h₀₁R h₁₁R
  · exact (hcross h₀₀pos h₁₁neg h₀₀R h₁₁R).trans hUVi
  · exact (hcross h₀₁pos h₁₀neg h₀₁R h₁₀R).trans ((inter_comm V U).trans hUVi)
  · rw [hposUnion, hnegUnion]
    ext x
    constructor
    · exact fun hx => hx.elim And.left And.left
    · intro hx
      rcases le_total 0 (A x) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩

end Geometry.SimplicialComplex
