import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import Mathlib.Order.Interval.Set.OrdConnectedLinear

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

theorem ChainShape.exists_active_eq {J : Set ℤ} (hne : J.Nonempty)
    (hJ : OrdConnected J) : ∃ shape : ChainShape, shape.active = J := by
  by_cases hlo : BddBelow J
  · by_cases hhi : BddAbove J
    · exact ⟨.finite (sInf J) (sSup J),
        ((hne.ordConnected_iff_of_bdd hlo hhi).mp hJ).symm⟩
    · refine ⟨.forward (sInf J), Subset.antisymm ?_ ?_⟩
      · intro i hi
        obtain ⟨j, hj, hij⟩ := not_bddAbove_iff.mp hhi i
        exact hJ.out (Int.csInf_mem hne hlo) hj ⟨hi, hij.le⟩
      · intro i hi
        exact csInf_le hlo hi
  · by_cases hhi : BddAbove J
    · refine ⟨.backward (sSup J), Subset.antisymm ?_ ?_⟩
      · intro i hi
        obtain ⟨j, hj, hji⟩ := not_bddBelow_iff.mp hlo i
        exact hJ.out hj (Int.csSup_mem hne hhi) ⟨hji.le, hi⟩
      · intro i hi
        exact le_csSup hhi hi
    · refine ⟨.biInfinite, Subset.antisymm ?_ (subset_univ _)⟩
      intro i _
      obtain ⟨a, ha, hai⟩ := not_bddBelow_iff.mp hlo i
      obtain ⟨b, hb, hib⟩ := not_bddAbove_iff.mp hhi i
      exact hJ.out ha hb ⟨hai.le, hib.le⟩

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

theorem exists_limit (C : ℕ → BalancedNeckChain g ε)
    (hincreasing : Monotone (fun n => (C n).shape.active))
    (hagree : ∀ n m, n ≤ m → ∀ i ∈ (C n).shape.active,
      (C n).neck i = (C m).neck i) :
    ∃ L : BalancedNeckChain g ε,
      L.shape.active = ⋃ n, (C n).shape.active ∧
      L.source_necks = ⋃ n, (C n).source_necks ∧
      (∀ n, ∀ i ∈ (C n).shape.active, L.neck i = (C n).neck i) ∧
      (⋃ i : {i // i ∈ L.shape.active}, (L.neck i.1).carrier) =
        ⋃ n, ⋃ i : {i // i ∈ (C n).shape.active}, ((C n).neck i.1).carrier := by
  classical
  let J : Set ℤ := ⋃ n, (C n).shape.active
  have hne : J.Nonempty := (C 0).active_nonempty.mono (subset_iUnion _ 0)
  have hJ : OrdConnected J := by
    constructor
    intro i hi j hj k hk
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    obtain ⟨m, hm⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨max n m, (C (max n m)).shape.ordConnected_active.out
      (hincreasing (le_max_left n m) hn) (hincreasing (le_max_right n m) hm) hk⟩
  obtain ⟨shape, hshape⟩ := ChainShape.exists_active_eq hne hJ
  have stage (i : ℤ) (hi : i ∈ J) : ∃ n, i ∈ (C n).shape.active := mem_iUnion.mp hi
  let N : ℤ → EpsilonNeck g := fun i =>
    if hi : i ∈ J then (C (stage i hi).choose).neck i else (C 0).neck i
  have hN (n : ℕ) (i : ℤ) (hi : i ∈ (C n).shape.active) : N i = (C n).neck i := by
    have hij : i ∈ J := mem_iUnion.mpr ⟨n, hi⟩
    dsimp only [N]
    rw [dif_pos hij]
    exact (hagree _ _ (le_max_left _ n) i (stage i hij).choose_spec).trans
      (hagree n _ (le_max_right _ n) i hi).symm
  have common (i j : ℤ) (hi : i ∈ shape.active) (hj : j ∈ shape.active) :
      ∃ n, i ∈ (C n).shape.active ∧ j ∈ (C n).shape.active := by
    obtain ⟨n, hn⟩ := stage i (hshape ▸ hi)
    obtain ⟨m, hm⟩ := stage j (hshape ▸ hj)
    exact ⟨max n m, hincreasing (le_max_left n m) hn,
      hincreasing (le_max_right n m) hm⟩
  let L : BalancedNeckChain g ε := {
    shape := shape
    neck := N
    source_necks := ⋃ n, (C n).source_necks
    selected := by
      intro i hi
      obtain ⟨n, hn⟩ := stage i (hshape ▸ hi)
      obtain ⟨S, hS, hsame⟩ := (C n).selected i hn
      exact ⟨S, mem_iUnion.mpr ⟨n, hS⟩, hN n i hn ▸ hsame⟩
    active_nonempty := hshape.symm ▸ hne
    epsilon_eq := by
      intro i hi
      obtain ⟨n, hn⟩ := stage i (hshape ▸ hi)
      rw [hN n i hn]
      exact (C n).epsilon_eq i hn
    centers_distinct := by
      intro i hi j hj hij
      obtain ⟨n, hni, hnj⟩ := common i j hi hj
      rw [hN n i hni, hN n j hnj]
      exact (C n).centers_distinct hni hnj hij
    adjacent_overlap := by
      intro i hi hj
      obtain ⟨n, hni, hnj⟩ := common i (i + 1) hi hj
      rw [hN n i hni, hN n (i + 1) hnj]
      exact (C n).adjacent_overlap i hni hnj
    overlap_contains_quarters := by
      intro i hi hj
      obtain ⟨n, hni, hnj⟩ := common i (i + 1) hi hj
      rw [hN n i hni, hN n (i + 1) hnj]
      exact (C n).overlap_contains_quarters i hni hnj
    overlap_within_three_quarters := by
      intro i hi hj
      obtain ⟨n, hni, hnj⟩ := common i (i + 1) hi hj
      rw [hN n i hni, hN n (i + 1) hnj]
      exact (C n).overlap_within_three_quarters i hni hnj
    later_disjoint_negative_end := by
      intro i hi j hj hij
      obtain ⟨n, hni, hnj⟩ := common i j hi hj
      rw [hN n i hni, hN n j hnj]
      exact (C n).later_disjoint_negative_end i hni j hnj hij
    balanced_center_distance := by
      intro i hi hj
      obtain ⟨n, hni, hnj⟩ := common i (i + 1) hi hj
      rw [hN n i hni, hN n (i + 1) hnj]
      exact (C n).balanced_center_distance i hni hnj }
  refine ⟨L, hshape, rfl, hN, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := stage i.1 (hshape ▸ i.2)
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨i.1, hn⟩, hN n i.1 hn ▸ hi⟩⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hn
    refine mem_iUnion.mpr ⟨⟨i.1, hshape.symm ▸ mem_iUnion.mpr ⟨n, i.2⟩⟩, ?_⟩
    change x ∈ (N i.1).carrier
    rwa [hN n i.1 i.2]

end BalancedNeckChain

end PoincareConjecture
