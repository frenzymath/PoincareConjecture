import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions
import PoincareConjecture.Proofs.M76.Mathlib.CompactZeroFiberBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHeightIntervalRestriction










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}






theorem exists_two_side_height_band
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (A : E →ᵃ[ℝ] ℝ) {p q : E} (hpq : p ≠ q)
    (hzero : P.boundary ℝ ∩ {x | A x = 0} = {p, q})
    (hsigns : ∀ x ∈ P.boundary ℝ, A x = 0 →
      x ∈ closure (P.boundary ℝ ∩ {y | 0 < A y}) ∧
      x ∈ closure (P.boundary ℝ ∩ {y | A y < 0}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∃ l r : Set E,
      Disjoint l r ∧ P.boundary ℝ ∩ {x | A x ∈ Icc (-δ) δ} = l ∪ r ∧
      ∃ d₀ : Icc (-δ) δ ≃ₜ l, ∃ d₁ : Icc (-δ) δ ≃ₜ r,
        d₀.IsFinitePL ∧ d₁.IsFinitePL ∧
        (∀ t, A (d₀ t) = (t : ℝ)) ∧ (∀ t, A (d₁ t) = (t : ℝ)) ∧
        (∀ hz : (0 : ℝ) ∈ Icc (-δ) δ, (d₀ ⟨0, hz⟩ : E) = p) ∧
        (∀ hz : (0 : ℝ) ∈ Icc (-δ) δ, (d₁ ⟨0, hz⟩ : E) = q) := by
  have hp := hzero.symm.subset (mem_insert p {q})
  have hq := hzero.symm.subset (mem_insert_of_mem p (mem_singleton q))
  obtain ⟨ap, bp, hap, hbp, Np, hNp, dp, hdp, hdpA, hdp0, hplocal⟩ :=
    P.exists_local_height_chart_of_both_signs hP hinj A hp.1 hp.2
      (hsigns p hp.1 hp.2).1 (hsigns p hp.1 hp.2).2
  obtain ⟨aq, bq, haq, hbq, Nq, hNq, dq, hdq, hdqA, hdq0, hqlocal⟩ :=
    P.exists_local_height_chart_of_both_signs hP hinj A hq.1 hq.2
      (hsigns q hq.1 hq.2).1 (hsigns q hq.1 hq.2).2
  have hNpc : IsCompact Np := isCompact_iff_compactSpace.mpr dp.compactSpace
  have hNqc : IsCompact Nq := isCompact_iff_compactSpace.mpr dq.compactSpace
  have hunique {N : Set E} {a b : ℝ} (d : Icc a b ≃ₜ N)
      (hdA : ∀ t, A (d t) = (t : ℝ)) {z : E}
      (hz : (0 : ℝ) ∈ Icc a b) (hd0 : (d ⟨0, hz⟩ : E) = z)
      {x : E} (hx : x ∈ N) (hAx : A x = 0) : x = z := by
    have ht : (d.symm ⟨x, hx⟩ : ℝ) = 0 := by
      rw [← hdA, d.apply_symm_apply]
      exact hAx
    calc
      x = (d (d.symm ⟨x, hx⟩) : E) :=
        (congrArg Subtype.val (d.apply_symm_apply ⟨x, hx⟩)).symm
      _ = d ⟨0, hz⟩ := congrArg (fun t => (d t : E)) (Subtype.ext ht)
      _ = z := hd0
  let U : Set E := interior {x | x ∈ P.boundary ℝ → x ∈ Np ∪ Nq}
  have hpU : p ∈ U := mem_interior_iff_mem_nhds.mpr
    (hplocal.mono fun x hx hxP => Or.inl (hx.mp hxP))
  have hqU : q ∈ U := mem_interior_iff_mem_nhds.mpr
    (hqlocal.mono fun x hx hxP => Or.inr (hx.mp hxP))
  have hzeroU : P.boundary ℝ ∩ {x | A x = 0} ⊆ U := by
    rw [hzero]
    exact pair_subset hpU hqU
  obtain ⟨η, hη, hηband⟩ :=
    P.isCompact_boundary.exists_pos_abs_le_subset_of_zero_fiber
      isOpen_interior A.continuous_of_finiteDimensional.continuousOn hzeroU
  have hnozero : (Np ∩ Nq) ∩ {x | A x = 0} ⊆ (∅ : Set E) := by
    intro x hx
    have hxp := hunique dp hdpA ⟨hap.le, hbp.le⟩ (hdp0 _) hx.1.1 hx.2
    have hxq := hunique dq hdqA ⟨haq.le, hbq.le⟩ (hdq0 _) hx.1.2 hx.2
    exact (hpq (hxp.symm.trans hxq)).elim
  obtain ⟨θ, hθ, hθband⟩ :=
    (hNpc.inter_right hNqc.isClosed).exists_pos_abs_le_subset_of_zero_fiber
      isOpen_empty A.continuous_of_finiteDimensional.continuousOn hnozero
  let δ := min ε (min η (min θ (min (-ap) (min bp (min (-aq) bq))))) / 2
  have hm : 0 < min ε (min η (min θ (min (-ap) (min bp (min (-aq) bq))))) := by
    simp only [lt_min_iff, neg_pos]
    exact ⟨hε, hη, hθ, hap, hbp, haq, hbq⟩
  have hδ : 0 < δ := half_pos hm
  have hδm : δ < min ε (min η (min θ (min (-ap) (min bp (min (-aq) bq))))) :=
    half_lt_self hm
  simp only [lt_min_iff] at hδm
  obtain ⟨hδε, hδη, hδθ, hδap, hδbp, hδaq, hδbq⟩ := hδm
  have hsubp : Icc (-δ) δ ⊆ Icc ap bp := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsubq : Icc (-δ) δ ⊆ Icc aq bq := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let l := Np ∩ {x | A x ∈ Icc (-δ) δ}
  let r := Nq ∩ {x | A x ∈ Icc (-δ) δ}
  have hdisj : Disjoint l r := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hθband x ⟨hx.1, hy.1⟩ ((abs_le.mpr hx.2).trans hδθ.le)
  have hcover : P.boundary ℝ ∩ {x | A x ∈ Icc (-δ) δ} = l ∪ r := by
    apply Subset.antisymm
    · intro x hx
      have hxU := hηband x hx.1 ((abs_le.mpr hx.2).trans hδη.le)
      rcases interior_subset hxU hx.1 with hxp | hxq
      · exact Or.inl ⟨hxp, hx.2⟩
      · exact Or.inr ⟨hxq, hx.2⟩
    · rintro x (hx | hx)
      · exact ⟨hNp hx.1, hx.2⟩
      · exact ⟨hNq hx.1, hx.2⟩
  obtain ⟨d₀, hd₀, hd₀A, hd₀val⟩ := hdp.exists_heightInterval_restriction A hdpA hsubp
  obtain ⟨d₁, hd₁, hd₁A, hd₁val⟩ := hdq.exists_heightInterval_restriction A hdqA hsubq
  exact ⟨δ, hδ, hδε, l, r, hdisj, hcover, d₀, d₁, hd₀, hd₁, hd₀A, hd₁A,
    fun hz => (hd₀val ⟨0, hz⟩).trans (hdp0 _),
    fun hz => (hd₁val ⟨0, hz⟩).trans (hdq0 _)⟩

end Polygon
