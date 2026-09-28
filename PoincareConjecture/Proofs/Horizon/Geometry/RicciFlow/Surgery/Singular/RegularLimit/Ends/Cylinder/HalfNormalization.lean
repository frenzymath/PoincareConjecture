import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.ClosedHalf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {U : Set M}

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem disjoint_tail_opposite_closedHalf (Q : OpenCylinderModel U) (side : Bool) :
    Disjoint (Q.tail side (1 / 2)) (Q.closedTail (!side) (1 / 2)) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  rw [disjoint_left]
  intro x hx hy
  have hx := ((Q.mem_tail_iff side hhalf).mp hx).2
  have hy := ((Q.mem_closedTail_iff (!side) hhalf).mp hy).2
  cases side <;> exact not_le_of_gt hx hy

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem not_closedHalf_subset_compact (Q : OpenCylinderModel U) (side : Bool)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ¬ Q.closedTail side (1 / 2) ⊆ K := by
  intro hsub
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨δ, hδ, hlow, hhigh, _, _⟩ := Q.exists_tails_disjoint_of_isCompact hK hKU
  have hδone : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, by linarith [hδ.2]⟩
  have hδcomp : 1 - δ ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hδ.1, hδ.2]
  cases side
  · obtain ⟨x, hx⟩ := (Q.isConnected_tail false hδone).nonempty
    have hx' := (Q.mem_tail_iff false hδone).mp hx
    exact disjoint_left.mp hlow hx (hsub ((Q.mem_closedTail_iff false hhalf).mpr
      ⟨hx'.1, hx'.2.le.trans hδ.2.le⟩))
  · obtain ⟨x, hx⟩ := (Q.isConnected_tail true hδcomp).nonempty
    have hx' := (Q.mem_tail_iff true hδcomp).mp hx
    have hxt : 1 - δ < (Q.inverse x).2 := hx'.2
    have hδhalf : δ < 1 / 2 := hδ.2
    exact disjoint_left.mp hhigh hx (hsub ((Q.mem_closedTail_iff true hhalf).mpr
      ⟨hx'.1, by change 1 / 2 ≤ (Q.inverse x).2; linarith only [hxt, hδhalf]⟩))

omit [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem isClosed_closedTail_of_subset (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {Y : Set M}
    (hY : IsClosed Y) (hYU : Y ⊆ U) (hsub : Q.closedTail side a ⊆ Y) :
    IsClosed (Q.closedTail side a) := by
  let S : Set ℝ := if side then Ici a else Iic a
  have hS : IsClosed S := by cases side <;> simp [S, isClosed_Ici, isClosed_Iic]
  have heq : Q.closedTail side a = Y ∩ (fun x => (Q.inverse x).2) ⁻¹' S := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub hx, ?_⟩
      have hx := ((Q.mem_closedTail_iff side ha).mp hx).2
      cases side <;> exact hx
    · rintro ⟨hxY, hx⟩
      apply (Q.mem_closedTail_iff side ha).mpr
      refine ⟨hYU hxY, ?_⟩
      cases side <;> exact hx
  rw [heq]
  exact (Q.inverse_smooth.continuousOn.snd.mono hYU).preimage_isClosed_of_isClosed hY hS

theorem exists_closedHalf_inside_closedTail (Q P : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hclosed : IsClosed (Q.closedTail side a))
    (hmid : P.middleSphere ⊆ Q.closedTail side a) :
    ∃ newSide : Bool,
      IsClosed (P.closedTail newSide (1 / 2)) ∧
      P.closedTail newSide (1 / 2) ⊆ Q.closedTail side a ∧
      ∃ b ∈ Ioo (0 : ℝ) 1, Q.tail side b ⊆ P.closedTail newSide (1 / 2) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hYU : Q.closedTail side a ⊆ U := fun _ hx => ((Q.mem_closedTail_iff side ha).mp hx).1
  have houtside : U \ Q.closedTail side a = Q.tail (!side) a := by
    ext x
    rw [mem_sdiff, Q.mem_closedTail_iff side ha, Q.mem_tail_iff (!side) ha]
    cases side <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
      constructor
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, lt_of_not_ge (fun hle => hx ⟨hxU, hle⟩)⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, fun h => not_le_of_gt hx h.2⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, lt_of_not_ge (fun hle => hx ⟨hxU, hle⟩)⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, fun h => not_le_of_gt hx h.2⟩
  have houtconn : IsConnected (U \ Q.closedTail side a) :=
    houtside.symm ▸ Q.isConnected_tail (!side) ha
  have houtavoid : Disjoint (U \ Q.closedTail side a) P.middleSphere :=
    disjoint_left.mpr fun _ hx hS => hx.2 (hmid hS)
  obtain ⟨σ, hσ⟩ := P.exists_side_of_connected houtconn sdiff_subset hhalf houtavoid
  have hsub : P.closedTail (!σ) (1 / 2) ⊆ Q.closedTail side a := by
    intro x hx
    by_contra hxY
    exact disjoint_left.mp (disjoint_tail_opposite_closedHalf P σ)
      (hσ ⟨((P.mem_closedTail_iff (!σ) hhalf).mp hx).1, hxY⟩) hx
  refine ⟨!σ, P.isClosed_closedTail_of_subset (!σ) hhalf hclosed hYU hsub, hsub, ?_⟩
  have hmidU : P.middleSphere ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact P.coordinate_mem ⟨mem_univ _, hz.2 ▸ hhalf⟩
  obtain ⟨δ, hδ, hlow, hhigh, _, _⟩ :=
    Q.exists_tails_disjoint_of_isCompact (P.isCompact_axial_sphere hhalf) hmidU
  let b : ℝ := if side then max (1 - δ) a else min δ a
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    cases side <;> dsimp [b]
    · exact ⟨lt_min hδ.1 ha.1, (min_le_right _ _).trans_lt ha.2⟩
    · exact ⟨ha.1.trans_le (le_max_right _ _), max_lt (by linarith [hδ.1]) ha.2⟩
  have havoid : Disjoint (Q.tail side b) P.middleSphere := by
    have hbase : Disjoint (Q.tail side (if side then 1 - δ else δ)) P.middleSphere := by
      cases side
      · exact hlow
      · exact hhigh
    apply hbase.mono_left
    intro x hx
    have hx := (Q.mem_tail_iff side hb).mp hx
    have ht : (if side then 1 - δ else δ) ∈ Ioo (0 : ℝ) 1 := by
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        constructor <;> linarith [hδ.1, hδ.2]
    apply (Q.mem_tail_iff side ht).mpr
    refine ⟨hx.1, ?_⟩
    cases side
    · exact hx.2.trans_le (min_le_left _ _)
    · exact (le_max_left _ _).trans_lt hx.2
  obtain ⟨τ, hτ⟩ := P.exists_side_of_connected (Q.isConnected_tail side hb)
    (Q.tail_subset side hb) hhalf havoid
  have hneq : τ ≠ σ := by
    intro heq
    subst τ
    let K := Q.coordinate '' (univ ×ˢ Icc (min a b) (max a b))
    have hK : IsCompact K := Q.isCompact_coordinate_slab (lt_min ha.1 hb.1) (max_lt ha.2 hb.2)
    have hKU : K ⊆ U := Q.coordinate_slab_subset (lt_min ha.1 hb.1) (max_lt ha.2 hb.2)
    apply not_closedHalf_subset_compact P (!σ) hK hKU
    intro x hx
    have hxY := (Q.mem_closedTail_iff side ha).mp (hsub hx)
    have hxnot : x ∉ Q.tail side b := fun ht =>
      disjoint_left.mp (disjoint_tail_opposite_closedHalf P σ) (hτ ht) hx
    have hxb : ¬ (if side then b < (Q.inverse x).2 else (Q.inverse x).2 < b) :=
      fun ht => hxnot ((Q.mem_tail_iff side hb).mpr ⟨hxY.1, ht⟩)
    refine ⟨Q.inverse x, ⟨mem_univ _, ?_⟩, Q.right_inverse hxY.1⟩
    cases side
    · exact ⟨(min_le_right _ _).trans (le_of_not_gt hxb), hxY.2.trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans hxY.2, (le_of_not_gt hxb).trans (le_max_right _ _)⟩
  have heq : τ = !σ := by cases τ <;> cases σ <;> simp_all
  exact ⟨b, hb, fun x hx => P.tail_subset_closedTail (!σ) hhalf (heq ▸ hτ hx)⟩

end PoincareConjecture.OpenCylinderModel
