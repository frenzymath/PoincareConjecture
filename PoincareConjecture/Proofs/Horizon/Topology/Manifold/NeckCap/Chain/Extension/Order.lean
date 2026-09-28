import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Limit

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

def IsExtension (C D : BalancedNeckChain g ε) : Prop :=
  C.shape.active ⊆ D.shape.active ∧ C.source_necks ⊆ D.source_necks ∧
    ∀ i ∈ C.shape.active, C.neck i = D.neck i

@[refl] theorem IsExtension.refl (C : BalancedNeckChain g ε) : C.IsExtension C :=
  ⟨Subset.rfl, Subset.rfl, fun _ _ => rfl⟩

@[trans] theorem IsExtension.trans {C D E : BalancedNeckChain g ε}
    (hCD : C.IsExtension D) (hDE : D.IsExtension E) : C.IsExtension E :=
  ⟨hCD.1.trans hDE.1, hCD.2.1.trans hDE.2.1,
    fun i hi => (hCD.2.2 i hi).trans (hDE.2.2 i (hCD.1 hi))⟩

theorem exists_directed_limit {ι : Type*} [Nonempty ι]
    (C : ι → BalancedNeckChain g ε) (hdir : Directed IsExtension C) :
    ∃ L : BalancedNeckChain g ε,
      L.shape.active = ⋃ n, (C n).shape.active ∧
      L.source_necks = ⋃ n, (C n).source_necks ∧
      (∀ n, (C n).IsExtension L) ∧
      (⋃ i : {i // i ∈ L.shape.active}, (L.neck i.1).carrier) =
        ⋃ n, ⋃ i : {i // i ∈ (C n).shape.active}, ((C n).neck i.1).carrier := by
  classical
  let n₀ : ι := Classical.choice inferInstance
  let J : Set ℤ := ⋃ n, (C n).shape.active
  have hne : J.Nonempty := (C n₀).active_nonempty.mono (subset_iUnion _ n₀)
  have hJ : OrdConnected J := by
    constructor
    intro i hi j hj k hk
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    obtain ⟨m, hm⟩ := mem_iUnion.mp hj
    obtain ⟨p, hnp, hmp⟩ := hdir n m
    exact mem_iUnion.mpr ⟨p, (C p).shape.ordConnected_active.out
      (hnp.1 hn) (hmp.1 hm) hk⟩
  obtain ⟨shape, hshape⟩ := ChainShape.exists_active_eq hne hJ
  have stage (i : ℤ) (hi : i ∈ J) : ∃ n, i ∈ (C n).shape.active := mem_iUnion.mp hi
  let N : ℤ → EpsilonNeck g := fun i =>
    if hi : i ∈ J then (C (stage i hi).choose).neck i else (C n₀).neck i
  have hN (n : ι) (i : ℤ) (hi : i ∈ (C n).shape.active) : N i = (C n).neck i := by
    have hij : i ∈ J := mem_iUnion.mpr ⟨n, hi⟩
    dsimp only [N]
    rw [dif_pos hij]
    obtain ⟨p, hkp, hnp⟩ := hdir (stage i hij).choose n
    exact (hkp.2.2 i (stage i hij).choose_spec).trans (hnp.2.2 i hi).symm
  have common (i j : ℤ) (hi : i ∈ shape.active) (hj : j ∈ shape.active) :
      ∃ n, i ∈ (C n).shape.active ∧ j ∈ (C n).shape.active := by
    obtain ⟨n, hn⟩ := stage i (hshape ▸ hi)
    obtain ⟨m, hm⟩ := stage j (hshape ▸ hj)
    obtain ⟨p, hnp, hmp⟩ := hdir n m
    exact ⟨p, hnp.1 hn, hmp.1 hm⟩
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
  refine ⟨L, hshape, rfl, ?_, ?_⟩
  · intro n
    refine ⟨?_, subset_iUnion (fun n => (C n).source_necks) n,
      fun i hi => (hN n i hi).symm⟩
    intro i hi
    change i ∈ shape.active
    rw [hshape]
    exact mem_iUnion.mpr ⟨n, hi⟩
  · ext x
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

end PoincareConjecture.BalancedNeckChain
