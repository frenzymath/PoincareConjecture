import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.MarkedCoverInjection

set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem PairedSourceGeometry.slab_pi1_injective
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    {phi : C(H, H)} {a b : ℝ} (geometry : PairedSourceGeometry e phi a b)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
      ∀ x : sourceSlab phi uv.1 uv.2,
        Function.Injective (FundamentalGroup.map
          (ContinuousMap.inclusion (sourceSlab_subset phi uv.1 uv.2)) x) := by
  let : TopologicalSpace.MetrizableSpace ((Fin 2 → ℝ) ⧸ (L).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let A := sourceSurface phi (a : C)
  let B' := sourceSurface phi (b : C)
  let N := sourceSlab phi a b
  let M := sourceSlab phi b (a + p)
  have hA : IsClosed A := (sourceSurface_isCompact phi (a : C)).isClosed
  have hB : IsClosed B' := (sourceSurface_isCompact phi (b : C)).isClosed
  have hdis : Disjoint A B' := sourceSurface_disjoint_of_ordered_phases phi ha hab hb
  have hprepared (uv : ℝ × ℝ) (huv : uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ))) :
      ∃ hSN : A ∪ B' ⊆ sourceSlab phi uv.1 uv.2,
        (∀ x : ↥(A ∪ B'),
          ∃ c : OpenPartialHomeomorph (↥(A ∪ B') × Ico (0 : ℝ) 1)
              (sourceSlab phi uv.1 uv.2),
            collarBase x ∈ c.source ∧ ∀ y, collarBase y ∈ c.source →
              c (collarBase y) = Set.inclusion hSN y) ∧
        ∀ x : ↥(A ∪ B'), Function.Injective
          (FundamentalGroup.map (ContinuousMap.inclusion hSN) x) := by
    let he := geometry.domains uv huv
    have hends : sourceSurface phi (uv.1 : C) ∪ sourceSurface phi (uv.2 : C) = A ∪ B' := by
      rcases huv with rfl | rfl
      · rfl
      · simp only [AddCircle.coe_add_period, A, B', union_comm]
    have hf : frontier (sourceSlab phi uv.1 uv.2) =
        (sourceSlab phi uv.1 uv.2 ∩ frontier R) ∪ (A ∪ B') := by
      rw [geometry.frontiers uv huv, hends]
    obtain ⟨hSN, hc⟩ := exists_phase_union_local_collars he
      (he.closed.inter isClosed_frontier) hA hB hf hdis (by
        intro P hP x hx
        obtain ⟨s, hs, rfl⟩ : ∃ s ∈ ({uv.1, uv.2} : Set ℝ), P = sourceSurface phi (s : C) := by
          rcases huv with rfl | rfl
          · rcases hP with rfl | rfl
            · exact ⟨a, Or.inl rfl, rfl⟩
            · exact ⟨b, Or.inr rfl, rfl⟩
          · rcases hP with rfl | rfl
            · exact ⟨a + p, Or.inr rfl, by simp only [AddCircle.coe_add_period, A]⟩
            · exact ⟨b, Or.inl rfl, rfl⟩
        obtain ⟨ell, lambda, w, z, G, hw, hz, hlz, hxG, _, _, hGN, _, hGP⟩ :=
          geometry.corners uv huv s hs x ⟨hx.1, hx.2.2⟩
        exact ⟨G, ell, lambda, w, z, hw, hz, hlz, hxG, hGN, hGP⟩)
    refine ⟨hSN, hc, ?_⟩
    apply FundamentalGroup.inclusion_injective_of_disjoint_closed_union hA hB hdis rfl hSN
    · intro hAN x
      have hi := geometry.ambient_injective a (Or.inl rfl) x
      have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) =
          (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi uv.1 uv.2, X)).comp
            (ContinuousMap.inclusion hAN) := rfl
      rw [heq, FundamentalGroup.map_comp] at hi
      exact Function.Injective.of_comp hi
    · intro hBN x
      have hi := geometry.ambient_injective b (Or.inr rfl) x
      have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(B', X)) =
          (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi uv.1 uv.2, X)).comp
            (ContinuousMap.inclusion hBN) := rfl
      rw [heq, FundamentalGroup.map_comp] at hi
      exact Function.Injective.of_comp hi
  obtain ⟨hcover, hmeet⟩ := sourceSlab_complementary_partition phi ha hab hb
  obtain ⟨hSN, hcN, hpN⟩ := hprepared (a, b) (Or.inl rfl)
  obtain ⟨hSM, hcM, hpM⟩ := hprepared (b, a + p) (Or.inr rfl)
  have hlocalN : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧ ∀ y, collarBase y ∈ c.source →
          c (collarBase y) = Set.inclusion inter_subset_left y := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hcN
  have hlocalM : ∀ x : ↥(N ∩ M),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ M) × Ico (0 : ℝ) 1) M,
        collarBase x ∈ c.source ∧ ∀ y, collarBase y ∈ c.source →
          c (collarBase y) = Set.inclusion inter_subset_right y := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hcM
  have hpiN : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hpN
  have hpiM : ∀ x : ↥(N ∩ M), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x) := by
    generalize_proofs hNM
    revert hNM
    rw [hmeet]
    intro _
    exact hpM
  have hne : (N ∩ M).Nonempty := by
    rw [hmeet]
    exact (sourceSurface_nonempty phi (a : C) F0).mono subset_union_left
  obtain ⟨hN, hM⟩ := relative_closed_cover_sides_pi1_injective
    (sourceSlab_isCompact phi a b) (sourceSlab_isCompact phi b (a + p))
    (sourceSlab_subset phi a b) (sourceSlab_subset phi b (a + p))
    hcover hne hlocalN hlocalM hpiN hpiM
  intro uv huv
  rcases huv with rfl | rfl
  · exact hN
  · exact hM

theorem PairedSourceGeometry.slab_ambient_pi1_injective
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    {phi : C(H, H)} {a b : ℝ} (geometry : PairedSourceGeometry e phi a b)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
      ∀ x : sourceSlab phi uv.1 uv.2,
        Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi uv.1 uv.2, X)) x) := by
  intro uv huv x
  have h := (handle_ambient_pi1_injective
    (ContinuousMap.inclusion (sourceSlab_subset phi uv.1 uv.2) x)).comp
      (geometry.slab_pi1_injective F0 ha hab hb uv huv x)
  have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi uv.1 uv.2, X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)).comp
        (ContinuousMap.inclusion (sourceSlab_subset phi uv.1 uv.2)) := rfl
  rw [heq, FundamentalGroup.map_comp]
  exact h

end PoincareConjecture.M76.HamiltonIntervalTorus
