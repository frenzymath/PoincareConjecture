import PoincareConjecture.Proofs.M76.Wall.Mathlib.AffineUnionCorner
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts











set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph






theorem exists_original_union_corner_charts
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X E) (Q : OpenPartialHomeomorph X E)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (a b : E →ᴬ[ℝ] ℝ) (u w : E)
    (hau : a.contLinear u = 1) (hbw : b.contLinear w = 1)
    (haw : a.contLinear w = 0) {L D : Set X}
    (hL : ∀ y ∈ Q.source, y ∈ L ↔ 0 ≤ a (Q y))
    (hD : ∀ y ∈ Q.source, y ∈ D ↔ a (Q y) ≤ 0 ∧ 0 ≤ b (Q y)) :
    ∃ P U : OpenPartialHomeomorph X E,
      P.source = Q.source ∧ U.source = Q.source ∧
      (∀ i, (e i).symm.trans P ∈ piecewiseAffineGroupoid E) ∧
      (∀ i, (e i).symm.trans U ∈ piecewiseAffineGroupoid E) ∧
      (∀ y ∈ P.source, y ∈ D ↔ 0 ≤ (-a) (P y)) ∧
      (∀ y ∈ U.source, y ∈ L ∪ D ↔ 0 ≤ a (U y)) ∧
      (∀ y ∈ Q.source, y ∈ frontier D ↔
        (a (Q y) = 0 ∧ 0 ≤ b (Q y)) ∨ (b (Q y) = 0 ∧ a (Q y) ≤ 0)) ∧
      ∀ y ∈ Q.source, y ∈ frontier (L ∪ D) ↔
        (a (Q y) = 0 ∧ b (Q y) ≤ 0) ∨ (b (Q y) = 0 ∧ a (Q y) ≤ 0) := by
  let v := u - b.contLinear u • w
  have hav : a.contLinear v = 1 := by
    dsimp only [v]
    rw [map_sub, map_smul, hau, haw, smul_zero, sub_zero]
  have hbv : b.contLinear v = 0 := by
    dsimp only [v]
    rw [map_sub, map_smul, hbw]
    change b.contLinear u - b.contLinear u * 1 = 0
    ring
  have hanv : (-a).contLinear (-v) = 1 := by
    change -a.contLinear (-v) = 1
    rw [map_neg, neg_neg, hav]
  have hbnv : b.contLinear (-v) = 0 := by rw [map_neg, hbv, neg_zero]
  have hanw : (-a).contLinear w = 0 := by
    change -a.contLinear w = 0
    rw [haw, neg_zero]
  obtain ⟨P0, hP0PL, _, _, _, hPquad, hPold, hPnew⟩ :=
    (-a).exists_corner_straightening b (-v) w hanv hbnv hanw hbw
  obtain ⟨U0, hU0PL, _, _, _, hUunion, hUzero⟩ :=
    a.exists_union_corner_straightening b v w hav hbv haw hbw
  let P := Q.trans P0.toOpenPartialHomeomorph
  let U := Q.trans U0.toOpenPartialHomeomorph
  have hPs : P.source = Q.source := by
    change Q.source ∩ Q ⁻¹' (univ : Set E) = Q.source
    rw [preimage_univ, inter_univ]
  have hUs : U.source = Q.source := by
    change Q.source ∩ Q ⁻¹' (univ : Set E) = Q.source
    rw [preimage_univ, inter_univ]
  have hPhalf : ∀ y ∈ P.source, y ∈ D ↔ 0 ≤ (-a) (P y) := by
    intro y hy
    rw [hD y (hPs.subset hy)]
    change (a (Q y) ≤ 0 ∧ 0 ≤ b (Q y)) ↔ 0 ≤ (-a) (P0 (Q y))
    simpa only [ContinuousAffineMap.neg_apply, neg_nonneg] using hPquad (Q y)
  have hUhalf : ∀ y ∈ U.source, y ∈ L ∪ D ↔ 0 ≤ a (U y) := by
    intro y hy
    rw [mem_union, hL y (hUs.subset hy), hD y (hUs.subset hy)]
    change (0 ≤ a (Q y) ∨ a (Q y) ≤ 0 ∧ 0 ≤ b (Q y)) ↔ 0 ≤ a (U0 (Q y))
    rw [← hUunion]
    constructor
    · rintro (ha | ⟨_, hb⟩)
      · exact Or.inl ha
      · exact Or.inr hb
    · rintro (ha | hb)
      · exact Or.inl ha
      · by_cases ha : 0 ≤ a (Q y)
        · exact Or.inl ha
        · exact Or.inr ⟨(lt_of_not_ge ha).le, hb⟩
  have hPzero (z : E) : (-a) (P0 z) = 0 ↔
      (a z = 0 ∧ 0 ≤ b z) ∨ (b z = 0 ∧ a z ≤ 0) := by
    constructor
    · intro hz
      by_cases hb : 0 ≤ b (P0 z)
      · have h := (hPold z).mpr ⟨hz, hb⟩
        exact Or.inl ⟨neg_eq_zero.mp h.1, h.2⟩
      · have h := (hPnew z).mpr ⟨hz, (lt_of_not_ge hb).le⟩
        exact Or.inr ⟨h.1, neg_nonneg.mp h.2⟩
    · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
      · exact ((hPold z).mp ⟨by simp only [ContinuousAffineMap.neg_apply, ha, neg_zero], hb⟩).1
      · exact ((hPnew z).mp ⟨hb, neg_nonneg.mpr ha⟩).1
  have hane : a.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : a.toAffineMap.linear u = 1 := hau
    rw [h] at hval
    norm_num at hval
  have hanne : (-a).toAffineMap.linear ≠ 0 := by
    intro h
    have hval : (-a).toAffineMap.linear (-v) = 1 := hanv
    rw [h] at hval
    norm_num at hval
  have hPfront := P.isImage_frontier_of_affine_nonneg (-a) hanne hPhalf
  have hUfront := U.isImage_frontier_of_affine_nonneg a hane hUhalf
  refine ⟨P, U, hPs, hUs, ?_, ?_, hPhalf, hUhalf, ?_, ?_⟩
  · intro i
    simpa only [P, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hQ i) hP0PL
  · intro i
    simpa only [U, ← OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hQ i) hU0PL
  · intro y hy
    exact (hPfront.apply_mem_iff (hPs.symm.subset hy)).symm.trans (hPzero (Q y))
  · intro y hy
    exact (hUfront.apply_mem_iff (hUs.symm.subset hy)).symm.trans (hUzero (Q y))

end OpenPartialHomeomorph
