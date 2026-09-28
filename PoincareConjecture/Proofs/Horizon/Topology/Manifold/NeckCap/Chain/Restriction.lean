import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

namespace ChainShape

def truncate (shape : ChainShape) (i : ℤ) (n : ℕ) : ChainShape :=
  match shape with
  | .finite a b => .finite (max a (i - n)) (min b (i + n))
  | .forward a => .finite (max a (i - n)) (i + n)
  | .backward b => .finite (i - n) (min b (i + n))
  | .biInfinite => .finite (i - n) (i + n)

theorem truncate_active (shape : ChainShape) (i : ℤ) (n : ℕ) :
    (shape.truncate i n).active = shape.active ∩ Icc (i - n) (i + n) := by
  cases shape <;> ext j <;> simp only [truncate, active, mem_Icc, mem_Ici,
    mem_Iic, mem_univ, true_and, mem_inter_iff, max_le_iff, le_min_iff] <;> omega

theorem truncate_finite (shape : ChainShape) (i : ℤ) (n : ℕ) :
    ∃ a b, shape.truncate i n = .finite a b := by
  cases shape <;> exact ⟨_, _, rfl⟩

theorem truncate_active_monotone (shape : ChainShape) (i : ℤ) :
    Monotone (fun n => (shape.truncate i n).active) := by
  intro n m hnm j hj
  dsimp only at hj ⊢
  rw [truncate_active] at hj ⊢
  exact ⟨hj.1, by obtain ⟨hl, hu⟩ := hj.2; constructor <;> omega⟩

theorem iUnion_truncate_active (shape : ChainShape) (i : ℤ) :
    (⋃ n, (shape.truncate i n).active) = shape.active := by
  ext j
  simp only [mem_iUnion, truncate_active, mem_inter_iff, mem_Icc]
  constructor
  · rintro ⟨n, hj, _⟩
    exact hj
  · intro hj
    refine ⟨(j - i).natAbs, hj, ?_⟩
    have hl := Int.le_natAbs (a := -(j - i))
    rw [Int.natAbs_neg] at hl
    have hu := Int.le_natAbs (a := j - i)
    constructor <;> omega

end ChainShape

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

def restrict (C : BalancedNeckChain g ε) (shape : ChainShape)
    (hne : shape.active.Nonempty) (hsub : shape.active ⊆ C.shape.active) :
    BalancedNeckChain g ε where
  shape := shape
  neck := C.neck
  source_necks := C.source_necks
  selected i hi := C.selected i (hsub hi)
  active_nonempty := hne
  epsilon_eq i hi := C.epsilon_eq i (hsub hi)
  centers_distinct := fun _ hi _ hj hij => C.centers_distinct (hsub hi) (hsub hj) hij
  adjacent_overlap i hi hj := C.adjacent_overlap i (hsub hi) (hsub hj)
  overlap_contains_quarters i hi hj := C.overlap_contains_quarters i (hsub hi) (hsub hj)
  overlap_within_three_quarters i hi hj :=
    C.overlap_within_three_quarters i (hsub hi) (hsub hj)
  later_disjoint_negative_end i hi j hj hij :=
    C.later_disjoint_negative_end i (hsub hi) j (hsub hj) hij
  balanced_center_distance i hi hj := C.balanced_center_distance i (hsub hi) (hsub hj)

def truncate (C : BalancedNeckChain g ε) (i : ℤ) (hi : i ∈ C.shape.active)
    (n : ℕ) : BalancedNeckChain g ε :=
  C.restrict (C.shape.truncate i n)
    ⟨i, by rw [ChainShape.truncate_active]; exact ⟨hi, by constructor <;> omega⟩⟩
    (by rw [ChainShape.truncate_active]; exact inter_subset_left)

@[simp] theorem truncate_neck (C : BalancedNeckChain g ε) (i : ℤ)
    (hi : i ∈ C.shape.active) (n : ℕ) : (C.truncate i hi n).neck = C.neck := rfl

@[simp] theorem truncate_shape (C : BalancedNeckChain g ε) (i : ℤ)
    (hi : i ∈ C.shape.active) (n : ℕ) :
    (C.truncate i hi n).shape = C.shape.truncate i n := rfl

theorem truncate_unionOpen_monotone (C : BalancedNeckChain g ε) (i : ℤ)
    (hi : i ∈ C.shape.active) : Monotone (fun n => (C.truncate i hi n).unionOpen) := by
  intro n m hnm x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨⟨j.1, C.shape.truncate_active_monotone i hnm j.2⟩, hj⟩

theorem iUnion_truncate_union (C : BalancedNeckChain g ε) (i : ℤ)
    (hi : i ∈ C.shape.active) :
    (⋃ n, ((C.truncate i hi n).unionOpen : Set M)) = C.unionOpen := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    have hja : j.1 ∈ C.shape.active := by
      have h := j.2
      change j.1 ∈ (C.shape.truncate i n).active at h
      rw [ChainShape.truncate_active] at h
      exact h.1
    exact mem_iUnion.mpr ⟨⟨j.1, hja⟩, hj⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hja : j.1 ∈ ⋃ n, (C.shape.truncate i n).active := by
      rw [ChainShape.iUnion_truncate_active]
      exact j.2
    obtain ⟨n, hn⟩ := mem_iUnion.mp hja
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨j.1, hn⟩, hj⟩⟩

end BalancedNeckChain

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ}


def forwardHalf (C : BalancedNeckChain g ε) (hbi : C.shape = .biInfinite) (a : ℤ) :
    BalancedNeckChain g ε :=
  C.restrict (.forward a) ⟨a, by change a ≤ a; exact le_rfl⟩
    (by rw [hbi]; exact subset_univ _)


def backwardHalf (C : BalancedNeckChain g ε) (hbi : C.shape = .biInfinite) (a : ℤ) :
    BalancedNeckChain g ε :=
  C.restrict (.backward a) ⟨a, by change a ≤ a; exact le_rfl⟩
    (by rw [hbi]; exact subset_univ _)

@[simp] theorem forwardHalf_neck (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) : (C.forwardHalf hbi a).neck = C.neck := rfl

@[simp] theorem backwardHalf_neck (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) : (C.backwardHalf hbi a).neck = C.neck := rfl

@[simp] theorem forwardHalf_shape (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) : (C.forwardHalf hbi a).shape = .forward a := rfl

@[simp] theorem backwardHalf_shape (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) : (C.backwardHalf hbi a).shape = .backward a := rfl

theorem neck_subset_forwardHalf_union (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) :
    (C.neck a).carrier ⊆ (C.forwardHalf hbi a).unionOpen := by
  intro x hx
  exact mem_iUnion.mpr ⟨⟨a, by change a ≤ a; exact le_rfl⟩, hx⟩

theorem neck_subset_backwardHalf_union (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) :
    (C.neck a).carrier ⊆ (C.backwardHalf hbi a).unionOpen := by
  intro x hx
  exact mem_iUnion.mpr ⟨⟨a, by change a ≤ a; exact le_rfl⟩, hx⟩

theorem union_forwardHalf_backwardHalf (C : BalancedNeckChain g ε)
    (hbi : C.shape = .biInfinite) (a : ℤ) :
    ((C.forwardHalf hbi a).unionOpen : Set M) ∪ (C.backwardHalf hbi a).unionOpen =
      C.unionOpen := by
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨i.1, by rw [hbi]; trivial⟩, hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨i.1, by rw [hbi]; trivial⟩, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases le_total a i.1 with hai | hia
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i.1, hai⟩, hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i.1, hia⟩, hi⟩)

end BalancedNeckChain

end PoincareConjecture
