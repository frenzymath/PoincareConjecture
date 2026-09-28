import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.TubeSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

def closedTail (Q : OpenCylinderModel U) (side : Bool) (a : ℝ) : Set M :=
  Q.coordinate '' (univ ×ˢ if side then Ico a 1 else Ioc 0 a)

theorem mem_closedTail_iff (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {x : M} :
    x ∈ Q.closedTail side a ↔ x ∈ U ∧
      if side then a ≤ (Q.inverse x).2 else (Q.inverse x).2 ≤ a := by
  cases side
  · change x ∈ Q.coordinate '' (univ ×ˢ Ioc 0 a) ↔ x ∈ U ∧ (Q.inverse x).2 ≤ a
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hdom : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt ha.2⟩
      refine ⟨Q.coordinate_mem hdom, ?_⟩
      rw [Q.left_inverse hdom]
      exact hz.2.2
    · rintro ⟨hx, hle⟩
      exact ⟨Q.inverse x, ⟨mem_univ _, (Q.inverse_mem x hx).2.1, hle⟩,
        Q.right_inverse hx⟩
  · change x ∈ Q.coordinate '' (univ ×ˢ Ico a 1) ↔ x ∈ U ∧ a ≤ (Q.inverse x).2
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hdom : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
        ⟨mem_univ _, ha.1.trans_le hz.2.1, hz.2.2⟩
      refine ⟨Q.coordinate_mem hdom, ?_⟩
      rw [Q.left_inverse hdom]
      exact hz.2.1
    · rintro ⟨hx, hle⟩
      exact ⟨Q.inverse x, ⟨mem_univ _, hle, (Q.inverse_mem x hx).2.2⟩,
        Q.right_inverse hx⟩

theorem closedTail_subset_tail (Q : OpenCylinderModel U) (side : Bool)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : if side then a < b else b < a) : Q.closedTail side b ⊆ Q.tail side a := by
  intro x hx
  obtain ⟨hxU, hx⟩ := (Q.mem_closedTail_iff side hb).mp hx
  apply (Q.mem_tail_iff side ha).mpr
  refine ⟨hxU, ?_⟩
  cases side
  · exact hx.trans_lt hab
  · exact hab.trans_le hx

theorem tail_subset_closedTail (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : Q.tail side a ⊆ Q.closedTail side a := by
  intro x hx
  obtain ⟨hxU, hx⟩ := (Q.mem_tail_iff side ha).mp hx
  apply (Q.mem_closedTail_iff side ha).mpr
  refine ⟨hxU, ?_⟩
  cases side <;> exact hx.le

theorem isConnected_closedTail (Q : OpenCylinderModel U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : IsConnected (Q.closedTail side a) := by
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  cases side
  · apply (isConnected_univ.prod (isConnected_Ioc ha.1)).image
    apply Q.coordinate_smooth.continuousOn.mono
    exact fun _ hz => ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt ha.2⟩
  · apply (isConnected_univ.prod (isConnected_Ico ha.2)).image
    apply Q.coordinate_smooth.continuousOn.mono
    exact fun _ hz => ⟨mem_univ _, ha.1.trans_le hz.2.1, hz.2.2⟩

theorem isClosed_closedTail_of_tail_subset (Q : OpenCylinderModel U) (side : Bool)
    {Y : Set M} (hY : IsClosed Y) (hYU : Y ⊆ U)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : if side then a < b else b < a) (hsub : Q.tail side a ⊆ Y) :
    IsClosed (Q.closedTail side b) := by
  let S : Set ℝ := if side then Ici b else Iic b
  have hS : IsClosed S := by cases side <;> simp [S, isClosed_Ici, isClosed_Iic]
  have heq : Q.closedTail side b = Y ∩ (fun x => (Q.inverse x).2) ⁻¹' S := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub (Q.closedTail_subset_tail side ha hb hab hx), ?_⟩
      have hx := ((Q.mem_closedTail_iff side hb).mp hx).2
      cases side <;> exact hx
    · rintro ⟨hxY, hx⟩
      apply (Q.mem_closedTail_iff side hb).mpr
      refine ⟨hYU hxY, ?_⟩
      cases side <;> exact hx
  rw [heq]
  exact (Q.inverse_smooth.continuousOn.snd.mono hYU).preimage_isClosed_of_isClosed hY hS

end PoincareConjecture.OpenCylinderModel
