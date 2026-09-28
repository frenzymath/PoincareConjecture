import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapseHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactStripFrontier
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set

namespace CollarCollapse

variable {E X : Type*} [TopologicalSpace E] [Zero E]
  [TopologicalSpace X] [T2Space X]

theorem exists_supported_source_family {B : Set E} (hB : IsCompact B)
    {delta r : ℝ} (hr : 0 < r) (hwidth : 2 * r < delta)
    (c : E × ℝ → X) (hc : ContinuousOn c (B ×ˢ Icc (-delta) delta))
    (hi : Topology.IsEmbedding
      (fun z : (B ×ˢ Icc (-delta) delta : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (B ×ˢ Ioo (-delta) delta))) :
    ∃ D : C(unitInterval × X, X),
      (∀ y : X, D (0, y) = y) ∧
      (∀ (s : unitInterval) (z : E × ℝ), z ∈ B ×ˢ Icc (-delta) delta →
        D (s, c z) = c (z.1, move r s z.2)) ∧
      (∀ (s : unitInterval) (y : X),
        y ∉ c '' (B ×ˢ Ioo (-(2 * r)) (2 * r)) → D (s, y) = y) ∧
      (∀ (s : unitInterval) (x : E), x ∈ B → D (s, c (x, 0)) = c (x, 0)) ∧
      (∀ (s : unitInterval) (z : E × ℝ),
        z ∈ B ×ˢ ({-delta, delta} : Set ℝ) → D (s, c z) = c z) ∧
      ∀ z : E × ℝ, z ∈ B ×ˢ Icc (-r) r → D (1, c z) = c (z.1, 0) := by
  have hdelta : 0 < delta := by linarith
  let P : Set (E × ℝ) := B ×ˢ Icc (-delta) delta
  let A : Set X := c '' P
  have hA : IsCompact A := (hB.prod isCompact_Icc).image_of_continuousOn hc
  obtain ⟨k, hk, hleft, _, hkmap⟩ := hi.exists_inverse_on_image
  have hkA : Continuous (fun y : A => k y) := hk.domRestrict
  let q : unitInterval × A → P := fun z =>
    ⟨((k z.2).1, move r z.1 (k z.2).2),
      ⟨(hkmap z.2.property).1,
        move_mem_Icc hr.le z.1.property (hkmap z.2.property).2⟩⟩
  have hq : Continuous q := by
    have hkprod : Continuous (fun z : unitInterval × A => k z.2) :=
      hkA.comp continuous_snd
    have ht : Continuous (fun z : unitInterval × A =>
        move r z.1 (k z.2).2) :=
      (continuous_move r).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk hkprod.snd)
    exact (hkprod.fst.prodMk ht).subtype_mk _
  let G : C(unitInterval × A, X) := ⟨fun z => c (q z), hc.domRestrict.comp hq⟩
  let H : C(unitInterval × X, X) := ⟨Prod.snd, continuous_snd⟩
  have hendmem {t : ℝ} (ht : t ∈ ({-delta, delta} : Set ℝ)) :
      t ∈ Icc (-delta) delta := by
    rcases ht with ht | ht
    · rw [ht]
      exact ⟨le_rfl, by linarith⟩
    · rw [ht]
      exact ⟨by linarith, le_rfl⟩
  have hendmove (s : unitInterval) {t : ℝ}
      (ht : t ∈ ({-delta, delta} : Set ℝ)) : move r s t = t := by
    apply move_of_two_le_abs hr.le
    rcases ht with ht | ht
    · rw [ht, abs_neg, abs_of_pos hdelta]
      exact hwidth.le
    · rw [ht, abs_of_pos hdelta]
      exact hwidth.le
  have hfront : ∀ (s : unitInterval) (y : A), (y : X) ∈ frontier A →
      G (s, y) = H (s, y) := by
    intro s y hy
    obtain ⟨z, hz, hzy⟩ := frontier_compact_strip_subset_ends hB hc ho hy
    have hzP : z ∈ P := ⟨hz.1, hendmem hz.2⟩
    change c ((k y).1, move r s (k y).2) = (y : X)
    rw [← hzy, hleft z hzP, hendmove s hz.2]
  obtain ⟨D, hinner, houter⟩ :=
    ContinuousMap.exists_paste_of_eq_on_frontier hA.isClosed G H hfront
  have hvalue (s : unitInterval) (z : E × ℝ) (hz : z ∈ P) :
      D (s, c z) = c (z.1, move r s z.2) := by
    have h := hinner s ⟨c z, ⟨z, hz, rfl⟩⟩
    change D (s, c z) = c ((k (c z)).1, move r s (k (c z)).2) at h
    simpa only [hleft z hz] using h
  have hzero (y : X) : D (0, y) = y := by
    by_cases hy : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hvalue 0 z hz]
      change c (z.1, move r 0 z.2) = c z
      rw [move_zero]
    · exact houter 0 y (fun h => hy (interior_subset h))
  have hfixed (s : unitInterval) (y : X)
      (hy : y ∉ c '' (B ×ˢ Ioo (-(2 * r)) (2 * r))) : D (s, y) = y := by
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hyA
      have ht : 2 * r ≤ |z.2| := by
        by_contra ht
        have ht' : |z.2| < 2 * r := lt_of_not_ge ht
        exact hy ⟨z, ⟨hz.1, abs_lt.mp ht'⟩, rfl⟩
      rw [hvalue s z hz, move_of_two_le_abs hr.le ht]
    · exact houter s y (fun h => hyA (interior_subset h))
  refine ⟨D, hzero, hvalue, hfixed, ?_, ?_, ?_⟩
  · intro s x hx
    have hz : (x, (0 : ℝ)) ∈ P := ⟨hx, by constructor <;> linarith⟩
    rw [hvalue s (x, 0) hz]
    change c (x, move r s 0) = c (x, 0)
    rw [move_of_mem hr.le (show (0 : ℝ) ∈ Icc (-r) r by
      constructor <;> linarith), mul_zero]
  · intro s z hz
    rw [hvalue s z ⟨hz.1, hendmem hz.2⟩, hendmove s hz.2]
  · intro z hz
    have hzP : z ∈ P := ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    rw [hvalue 1 z hzP]
    change c (z.1, move r 1 z.2) = c (z.1, 0)
    rw [move_one, height_of_mem hr.le hz.2]

end CollarCollapse
