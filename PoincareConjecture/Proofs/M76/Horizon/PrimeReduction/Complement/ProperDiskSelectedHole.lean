import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ChosenHolePuncturedBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FinitePLBallAttachment

set_option autoImplicit false

open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem IsFinitePLBallPair.isConnected_boundary_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {d r : Set E}
    (hd : IsFinitePLBallPair V2 d r) : IsConnected r := by
  obtain ⟨c, _, hcr⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V2)
  let cb := c.restrictSubsets hd.1 isClosed_closedBall.frontier_subset hcr
  exact cb.isConnected_of_convex_frontier
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)

theorem IsConnected.exists_unique_subset_finite_disjoint_closed
    {X ι : Type*} [TopologicalSpace X] [Finite ι] {s : Set X}
    (hs : IsConnected s) (a : ι → Set X) (ha : ∀ i, IsClosed (a i))
    (hdis : Pairwise fun i j => Disjoint (a i) (a j))
    (hsa : s ⊆ ⋃ i, a i) : ∃! i, s ⊆ a i := by
  classical
  obtain ⟨x, hx⟩ := hs.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hsa hx)
  have hsep : Disjoint (a i) (⋃ j : {j : ι // j ≠ i}, a j) := by
    apply disjoint_left.mpr
    intro y hyi hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    exact disjoint_left.mp (hdis j.property) hyj hyi
  have hcover : s ⊆ a i ∪ ⋃ j : {j : ι // j ≠ i}, a j := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hsa hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hsub : s ⊆ a i := by
    have h := isPreconnected_iff_subset_of_disjoint_closed.mp hs.isPreconnected
      (a i) (⋃ j : {j : ι // j ≠ i}, a j) (ha i)
      (isClosed_iUnion_of_finite fun j => ha j) hcover
      (by rw [hsep.inter_eq, inter_empty])
    rcases h with h | h
    · exact h
    · exact False.elim (disjoint_left.mp hsep hxi (h hx))
  refine ⟨i, hsub, ?_⟩
  intro j hj
  by_contra hji
  exact disjoint_left.mp (hdis hji) (hj hx) hxi

theorem IsFinitePLBallPair.exists_selected_hole_for_proper_disk
    {ι : Type*} [Finite ι] (a r : ι → Set V4)
    (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haS : ∀ i, a i ⊆ sphere)
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a i \ r i)))
    (hdis : Pairwise fun i j => Disjoint (a i) (a j))
    {d b : Set V4} (hd : IsFinitePLBallPair V2 d b)
    (hdQ : d ⊆ sphere \ ⋃ i, a i \ r i)
    (hproper : d ∩ ⋃ i, r i = b) :
    ∃ i, (∀ j, b ⊆ r j ↔ j = i) ∧
      IsFinitePLBallPair V3 (sphere \ (a i \ r i)) (r i) ∧
      d ⊆ sphere \ (a i \ r i) ∧ d ∩ r i = b ∧
      d \ b ⊆ (sphere \ (a i \ r i)) \ r i ∧
      (∀ j, j ≠ i → Disjoint d (a j)) ∧
      (∀ j : {j : ι // j ≠ i}, a j ⊆ (sphere \ (a i \ r i)) \ r i) ∧
      ((sphere \ (a i \ r i)) \ ⋃ j : {j : ι // j ≠ i}, a j \ r j) =
        sphere \ ⋃ j, a j \ r j := by
  classical
  have hbcover : b ⊆ ⋃ i, a i := by
    intro x hx
    have hxrim : x ∈ ⋃ i, r i := (hproper.symm ▸ hx).2
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxrim
    exact mem_iUnion.mpr ⟨i, (ha i).1 hxi⟩
  obtain ⟨i, hbi, huniq⟩ :=
    hd.isConnected_boundary_two.exists_unique_subset_finite_disjoint_closed
      a (fun i => (ha i).isCompact.isClosed) hdis hbcover
  have hbri : b ⊆ r i := by
    intro x hx
    by_contra hxr
    exact (hdQ (hd.1 hx)).2 (mem_iUnion.mpr ⟨i, hbi hx, hxr⟩)
  have hdi : d ⊆ sphere \ (a i \ r i) := by
    intro x hx
    exact ⟨(hdQ hx).1, fun hi => (hdQ hx).2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have hdr : d ∩ r i = b := by
    apply Subset.antisymm
    · intro x hx
      exact hproper ▸ ⟨hx.1, mem_iUnion.mpr ⟨i, hx.2⟩⟩
    · exact fun x hx => ⟨hd.1 hx, hbri hx⟩
  obtain ⟨hball, hother, heq, _⟩ :=
    selected_hole_punctured_ball a r ha haS hopen hdis i
  refine ⟨i, ?_, hball, hdi, hdr, ?_, ?_, hother, heq⟩
  · intro j
    constructor
    · intro hj
      exact huniq j (hj.trans (ha j).1)
    · rintro rfl
      exact hbri
  · intro x hx
    exact ⟨hdi hx.1, fun hxr => hx.2 (hdr ▸ ⟨hx.1, hxr⟩)⟩
  · intro j hji
    apply disjoint_left.mpr
    intro x hxd hxj
    have hxr : x ∈ r j := by
      by_contra hxnr
      exact (hdQ hxd).2 (mem_iUnion.mpr ⟨j, hxj, hxnr⟩)
    have hxb : x ∈ b := hproper ▸ ⟨hxd, mem_iUnion.mpr ⟨j, hxr⟩⟩
    exact disjoint_left.mp (hdis hji) hxj (hbi hxb)

theorem open_support_avoiding_other_closed_holes
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (a : ι → Set X) (ha : ∀ i, IsClosed (a i)) (i : ι)
    {d : Set X} (hda : ∀ j, j ≠ i → Disjoint d (a j)) :
    IsOpen (⋃ j : {j : ι // j ≠ i}, a j)ᶜ ∧
      d ⊆ (⋃ j : {j : ι // j ≠ i}, a j)ᶜ ∧
      ∀ j, j ≠ i → Disjoint (⋃ k : {k : ι // k ≠ i}, a k)ᶜ (a j) := by
  refine ⟨(isClosed_iUnion_of_finite fun j : {j : ι // j ≠ i} => ha j).isOpen_compl,
    ?_, ?_⟩
  · intro x hx hxholes
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxholes
    exact disjoint_left.mp (hda j j.property) hx hxj
  · intro j hji
    exact disjoint_left.mpr fun _ hx hxj => hx (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)

end Set
