import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.NumericalAnnularCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace Poincare.CurvatureIntegral
theorem exists_finite_annuli_and_spire_cover_of_subset_transfer
    {X : ℕ → Type} [∀ j, MetricSpace (X j)]
    {Y : Type} [MetricSpace Y] (E : ∀ j, Set (X j))
    {K : Set Y}
    (f : ∀ j, Y → X j)
    (hpair : ∀ y z, Tendsto (fun j => dist (f j y) (f j z)) atTop (𝓝 (dist y z)))
    (hK : IsCompact K)
    (htransfer : ∀ {ι : Type} [Finite ι] (y : ι → Y) (r : ι → ℝ),
      K ⊆ ⋃ i, Metric.ball (y i) (r i) →
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
        E j ⊆ ⋃ i, Metric.ball (f j (y i)) (r i + η))
    (F S : Finset Y) (B : Y → ℝ)
    (hB : ∀ y ∈ F, 0 < B y ∧ B y ≤ 1)
    (hcover : K \ (S : Set Y) ⊆
      ⋃ y ∈ F, Metric.ball y (B y / 4) \ {y})
    (q : ∀ j, S → X j)
    (hq : ∀ i, Tendsto (fun j => dist (f j i.val) (q j i)) atTop (𝓝 0))
    (σ : S → ℝ) (hσ : ∀ i, 0 < σ i) :
    ∃ A : Finset (Y × ℝ),
      (∀ a ∈ A, a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ 3 * a.2 < 2 * B a.1) ∧
      (K ⊆
        (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist a.1 x ∧
          dist a.1 x ≤ (19 / 16 : ℝ) * a.2}) ∪ ⋃ i : S, Metric.ball i.val (σ i)) ∧
      ∀ᶠ j in atTop, E j ⊆
        (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist (f j a.1) x ∧
          dist (f j a.1) x ≤ (19 / 16 : ℝ) * a.2}) ∪
          ⋃ i : S, Metric.ball (q j i) (σ i) := by
  classical
  obtain ⟨E, e, he, hEc⟩ := exists_finite_annular_spire_ball_refinement
    hK F S B (fun y hy => (hB y hy).1) hcover σ hσ
  let J := E
  have hej (z : J) : 0 < e z.val := (he z.val z.property).1
  have htagEx (z : J) : ∃ t : S ⊕ (Y × ℝ),
      match t with
      | .inl i => dist i.val z.val.val + 4 * e z.val < σ i
      | .inr a => a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ B a.1 / 3 ∧
          (113 / 96 : ℝ) * a.2 + 4 * e z.val < dist a.1 z.val.val ∧
          dist a.1 z.val.val + 4 * e z.val < (19 / 16 : ℝ) * a.2 := by
    rcases (he z.val z.property).2 with ⟨i, hi⟩ | ⟨y, hy, r, hr, hrB, hlo, hhi⟩
    · exact ⟨.inl i, hi⟩
    · exact ⟨.inr (y, r), hy, hr, hrB, hlo, hhi⟩
  choose tag htag using htagEx
  let A : Finset (Y × ℝ) := (Finset.univ.image tag).toRight
  have hAmem (z : J) (a : Y × ℝ) (hz : tag z = .inr a) : a ∈ A := by
    apply Finset.mem_toRight.mpr
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩
  have hAbounds : ∀ a ∈ A,
      a.1 ∈ F ∧ 0 < a.2 ∧ a.2 ≤ 1 ∧ 3 * a.2 < 2 * B a.1 := by
    intro a ha
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp (Finset.mem_toRight.mp ha)
    have hzdata := htag z
    rw [hz] at hzdata
    have hBa := hB a.1 hzdata.1
    exact ⟨hzdata.1, hzdata.2.1, by linarith [hzdata.2.2.1],
      by linarith [hzdata.2.2.1]⟩
  have htarget : K ⊆
      (⋃ a ∈ A, {x | (113 / 96 : ℝ) * a.2 ≤ dist a.1 x ∧
        dist a.1 x ≤ (19 / 16 : ℝ) * a.2}) ∪ ⋃ i : S, Metric.ball i.val (σ i) := by
    intro x hx
    obtain ⟨z, hzE, hxz⟩ := mem_iUnion₂.mp (hEc hx)
    let zJ : J := ⟨z, hzE⟩
    have hez := hej zJ
    have hdist : dist z.val x < e z := Metric.mem_ball'.mp hxz
    have hzdata := htag zJ
    cases hz : tag zJ with
    | inl i =>
      rw [hz] at hzdata
      apply Or.inr
      refine mem_iUnion.mpr ⟨i, Metric.mem_ball'.mpr ?_⟩
      have ht := dist_triangle i.val z.val x
      change dist i.val z.val + 4 * e z < σ i at hzdata
      linarith
    | inr a =>
      rw [hz] at hzdata
      apply Or.inl
      refine mem_iUnion₂.mpr ⟨a, hAmem zJ a hz, ?_, ?_⟩
      · have ht := dist_triangle a.1 x z.val
        rw [dist_comm x z.val] at ht
        have hlo := hzdata.2.2.2.1
        change (113 / 96 : ℝ) * a.2 + 4 * e z < dist a.1 z.val at hlo
        linarith
      · have ht := dist_triangle a.1 z.val x
        have hhi := hzdata.2.2.2.2
        change dist a.1 z.val + 4 * e z < (19 / 16 : ℝ) * a.2 at hhi
        linarith
  let T : Finset ℝ := insert 1 (E.image e)
  have hT : T.Nonempty := ⟨1, by simp [T]⟩
  let η := T.min' hT
  have hη : 0 < η := by
    have hm : η ∈ T := Finset.min'_mem T hT
    rcases Finset.mem_insert.mp hm with h1 | hi
    · simpa only [h1] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨z, hzE, hz⟩ := Finset.mem_image.mp hi
      simpa only [hz] using (he z hzE).1
  have hηe (z : J) : η ≤ e z.val := Finset.min'_le T _ (by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩)
  have hfiniteCover : K ⊆
      ⋃ z : J, Metric.ball z.val.val (e z.val) := by
    intro x hx
    obtain ⟨z, hzE, hz⟩ := mem_iUnion₂.mp (hEc hx)
    exact mem_iUnion.mpr ⟨⟨z, hzE⟩, hz⟩
  have hsourceCover := htransfer (fun z : J => z.val.val) (fun z : J => e z.val)
    hfiniteCover η hη
  let cs : ∀ j, J → X j := fun j z =>
    match tag z with | .inl i => q j i | .inr a => f j a.1
  let ct : J → Y := fun z =>
    match tag z with | .inl i => i.val | .inr a => a.1
  have hcd (z : J) :
      Tendsto (fun j => dist (cs j z) (f j z.val.val)) atTop
        (𝓝 (dist (ct z) z.val.val)) := by
    cases hz : tag z with
    | inl i =>
      simp only [cs, ct, hz]
      apply (hpair i.val z.val.val).congr_dist
      exact squeeze_zero (fun _ => dist_nonneg)
        (fun j => dist_dist_dist_le_left (f j i.val) (q j i) (f j z.val.val)) (hq i)
    | inr a =>
      simp only [cs, ct, hz]
      exact hpair a.1 z.val.val
  have hclose : ∀ᶠ j in atTop, ∀ z : J,
      |dist (cs j z) (f j z.val.val) - dist (ct z) z.val.val| < e z.val := by
    apply eventually_all.mpr
    intro z
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hcd z) (e z.val) (hej z))
  refine ⟨A, hAbounds, htarget, ?_⟩
  filter_upwards [hsourceCover, hclose] with j hj hcj
  intro x hx
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hj hx)
  have hzx : dist (f j z.val.val) x < e z.val + η := Metric.mem_ball'.mp hz
  have hez := hej z
  have hηz := hηe z
  obtain ⟨hcLo, hcHi⟩ := abs_lt.mp (hcj z)
  have hUp := dist_triangle (cs j z) (f j z.val.val) x
  have hLo := dist_triangle (cs j z) x (f j z.val.val)
  rw [dist_comm x (f j z.val.val)] at hLo
  have hzdata := htag z
  cases ht : tag z with
  | inl i =>
    rw [ht] at hzdata
    apply Or.inr
    refine mem_iUnion.mpr ⟨i, Metric.mem_ball'.mpr ?_⟩
    simp only [cs, ct, ht] at hcLo hcHi hUp hLo
    linarith
  | inr a =>
    rw [ht] at hzdata
    apply Or.inl
    refine mem_iUnion₂.mpr ⟨a, hAmem z a ht, ?_, ?_⟩
    · simp only [cs, ct, ht] at hcLo hcHi hUp hLo
      linarith [hzdata.2.2.2.1]
    · simp only [cs, ct, ht] at hcLo hcHi hUp hLo
      linarith [hzdata.2.2.2.2]

end Poincare.CurvatureIntegral
