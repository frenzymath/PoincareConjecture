import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPartition
import PoincareConjecture.Proofs.M76.Mathlib.FiniteOrderedPartition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem FinitePiecewiseAffineOn.exists_interval_partition_four
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1)) :
    ∃ (n : ℕ) (t : Fin (n + 4) → ℝ), StrictMono t ∧ t 0 = 0 ∧
      t (Fin.last (n + 3)) = 1 ∧
      ∀ i : Fin (n + 3), ∃ A : ℝ →ᴬ[ℝ] E,
        EqOn f A (Icc (t i.castSucc) (t i.succ)) := by
  classical
  obtain ⟨B, hB, hB0, hB1, hformula⟩ := hf.exists_interval_breakpoints zero_le_one
  let Q : Finset ℝ := {0, 1 / 3, 2 / 3, 1}
  let T := B ∪ Q
  have hQT : Q ⊆ T := Finset.subset_union_right
  have hQcard : Q.card = 4 := by norm_num [Q]
  have hcard : 4 ≤ T.card := by
    rw [← hQcard]
    exact Finset.card_le_card hQT
  obtain ⟨n, hn⟩ : ∃ n, T.card = n + 4 := ⟨T.card - 4, by omega⟩
  let t := T.orderEmbOfFin hn
  have ht : StrictMono t := t.strictMono
  have hrange : range t = T := T.range_orderEmbOfFin hn
  have hT : (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hB hx
    · simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num
  have hmem (i : Fin (n + 4)) : t i ∈ Icc (0 : ℝ) 1 :=
    hT (T.orderEmbOfFin_mem hn i)
  have ht0 : t 0 = 0 := by
    have hzero : (0 : ℝ) ∈ T := Finset.mem_union_left _ hB0
    obtain ⟨i, hi⟩ := hrange.symm ▸ (show (0 : ℝ) ∈ (T : Set ℝ) from hzero)
    exact le_antisymm (hi ▸ ht.monotone (Fin.zero_le i)) (hmem 0).1
  have ht1 : t (Fin.last (n + 3)) = 1 := by
    have hone : (1 : ℝ) ∈ T := Finset.mem_union_left _ hB1
    obtain ⟨i, hi⟩ := hrange.symm ▸ (show (1 : ℝ) ∈ (T : Set ℝ) from hone)
    exact le_antisymm (hmem _).2 (hi ▸ ht.monotone (Fin.le_last i))
  refine ⟨n, t, ht, ht0, ht1, fun i => ?_⟩
  apply hformula _ _ (hmem _).1 (hmem _).2 (ht Fin.castSucc_lt_succ)
  apply Set.disjoint_left.mpr
  intro x hx hxB
  have hxT : x ∈ T := Finset.mem_union_left _ hxB
  obtain ⟨j, rfl⟩ := hrange.symm ▸ (show x ∈ (T : Set ℝ) from hxT)
  have hleft := ht.lt_iff_lt.mp hx.1
  have hright := ht.lt_iff_lt.mp hx.2
  have hleft' : i.val < j.val := hleft
  have hright' : j.val < i.val + 1 := hright
  omega

theorem FinitePiecewiseAffineOn.exists_simplicial_interval_path
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hfi : InjOn f (Icc (0 : ℝ) 1)) :
    ∃ (n : ℕ) (p : Fin (n + 4) → E), Function.Injective p ∧
      p 0 = f 0 ∧ p (Fin.last (n + 3)) = f 1 ∧
      Polygon.pathCarrier p = f '' Icc (0 : ℝ) 1 ∧
      (∀ i j : Fin (n + 3),
        segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
          convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ})) ∧
      ∀ (i : Fin (n + 3)) (j : Fin (n + 4)),
        p j ∈ segment ℝ (p i.castSucc) (p i.succ) →
          p j = p i.castSucc ∨ p j = p i.succ := by
  obtain ⟨n, t, ht, ht0, ht1, hformula⟩ := hf.exists_interval_partition_four
  let p := f ∘ t
  have hparam (i : Fin (n + 4)) : t i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le _)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last _)
  have hold (i : Fin (n + 3)) {x : ℝ}
      (hx : x ∈ Icc (t i.castSucc) (t i.succ)) : x ∈ Icc (0 : ℝ) 1 :=
    ⟨(hparam _).1.trans hx.1, hx.2.trans (hparam _).2⟩
  have hedge (i : Fin (n + 3)) : segment ℝ (p i.castSucc) (p i.succ) =
      f '' Icc (t i.castSucc) (t i.succ) := by
    obtain ⟨A, hA⟩ := hformula i
    have hle : t i.castSucc ≤ t i.succ := (ht Fin.castSucc_lt_succ).le
    have hleft := hA (left_mem_Icc.mpr hle)
    have hright := hA (right_mem_Icc.mpr hle)
    have hseg : A '' affineSegment ℝ (t i.castSucc) (t i.succ) =
        affineSegment ℝ (A (t i.castSucc)) (A (t i.succ)) :=
      affineSegment_image A.toAffineMap _ _
    rw [affineSegment_eq_segment, affineSegment_eq_segment, segment_eq_Icc hle] at hseg
    change segment ℝ (f (t i.castSucc)) (f (t i.succ)) = _
    rw [hleft, hright, ← hseg]
    exact hA.image_eq.symm
  have hpi : Function.Injective p := by
    intro i j hij
    exact ht.injective (hfi (hparam i) (hparam j) hij)
  have hcarrier : Polygon.pathCarrier p = f '' Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨y, hy, hyx⟩ := (hedge i) ▸ hi
      exact ⟨y, hold i hy, hyx⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ Icc (t 0) (t (Fin.last (n + 3))) := by rwa [ht0, ht1]
      obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hy'
      exact mem_iUnion.mpr ⟨i, (hedge i).symm ▸ mem_image_of_mem f hi⟩
  have hend (i : Fin (n + 3)) (x : ℝ)
      (hx : x = t i.castSucc ∨ x = t i.succ) :
      f x ∈ ({p i.castSucc, p i.succ} : Set E) := by
    rcases hx with rfl | rfl <;> simp only [p, Function.comp_apply, mem_insert_iff,
      mem_singleton_iff, true_or, or_true]
  refine ⟨n, p, hpi, congrArg f ht0, congrArg f ht1, hcarrier, ?_, ?_⟩
  · intro i j x hx
    by_cases hij : i = j
    · subst j
      simpa only [inter_self, convexHull_pair] using hx.1
    · obtain ⟨a, ha, hax⟩ := (hedge i) ▸ hx.1
      obtain ⟨b, hb, hbx⟩ := (hedge j) ▸ hx.2
      have hba : b = a := hfi (hold j hb) (hold i ha) (hbx.trans hax.symm)
      subst b
      obtain ⟨hi, hj⟩ := ht.eq_endpoints_of_mem_consecutive_Icc hij ha hb
      exact hax ▸ subset_convexHull ℝ _ ⟨hend i a hi, hend j a hj⟩
  · intro i j hj
    obtain ⟨x, hx, hxj⟩ := (hedge i) ▸ hj
    have hx' : x = t j := hfi (hold i hx) (hparam j) hxj
    subst x
    have hleft : i.castSucc ≤ j := ht.le_iff_le.mp hx.1
    have hright : j ≤ i.succ := ht.le_iff_le.mp hx.2
    have hleft' : i.val ≤ j.val := hleft
    have hright' : j.val ≤ i.val + 1 := hright
    have hj' : j = i.castSucc ∨ j = i.succ := by
      by_cases he : j.val = i.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext (by change j.val = i.val + 1; omega))
    exact hj'.imp (congrArg p) (congrArg p)

end Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_simplicial_path_with_endpoints
    {s : Set E} {a b : E} (hs : IsFinitePLBallPair ℝ s {a, b}) (hab : a ≠ b) :
    ∃ (n : ℕ) (p : Fin (n + 4) → E), Function.Injective p ∧
      p 0 = a ∧ p (Fin.last (n + 3)) = b ∧ Polygon.pathCarrier p = s ∧
      (∀ i j : Fin (n + 3),
        segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
          convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ})) ∧
      ∀ (i : Fin (n + 3)) (j : Fin (n + 4)),
        p j ∈ segment ℝ (p i.castSucc) (p i.succ) →
          p j = p i.castSucc ∨ p j = p i.succ := by
  obtain ⟨e, ⟨f, hf, hfe⟩, he0, he1⟩ := hs.exists_unitInterval_chart_with_endpoints hab
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have he : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hfe, hfe]
      exact hxy
    exact congrArg Subtype.val (e.injective he)
  have hfs : f '' Icc (0 : ℝ) 1 = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfe ⟨y, hy⟩ ▸ (e ⟨y, hy⟩).property
    · intro hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      exact ⟨y, y.property, (hfe y).symm.trans (congrArg Subtype.val hy)⟩
  obtain ⟨n, p, hp, hp0, hp1, hps, hinter, hvertex⟩ := hf.exists_simplicial_interval_path hfi
  refine ⟨n, p, hp, ?_, ?_, hps.trans hfs, hinter, hvertex⟩
  · exact hp0.trans ((hfe ⟨0, ⟨le_rfl, zero_le_one⟩⟩).symm.trans he0)
  · exact hp1.trans ((hfe ⟨1, ⟨zero_le_one, le_rfl⟩⟩).symm.trans he1)

end Set
