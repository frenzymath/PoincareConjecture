import PoincareConjecture.Proofs.M25.AppA_1_Necks.ChainShapeInterval
import Mathlib.Order.Monotone.Basic











set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.BalancedNeckChain




theorem exists_coherent_finite_limit
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (C : ℕ → BalancedNeckChain g epsilon) (a b : ℕ → ℤ)
    (hshape : ∀ n, (C n).shape = ChainShape.finite (a n) (b n))
    (hmono : ∀ n, (C n).shape.active ⊆ (C (n + 1)).shape.active)
    (hretain : ∀ n, ∀ i ∈ (C n).shape.active,
      (C (n + 1)).neck i = (C n).neck i)
    (hsource : ∀ n, (C n).source_necks = (C 0).source_necks) :
    ∃ D : BalancedNeckChain g epsilon,
      D.shape.active = (⋃ n, (C n).shape.active) ∧
      D.source_necks = (C 0).source_necks ∧
      ∀ n, ∀ i ∈ (C n).shape.active, D.neck i = (C n).neck i := by
  classical
  have hmonoAll : Monotone (fun n => (C n).shape.active) := monotone_nat_of_le_succ hmono
  have hretainAll {n m : ℕ} (hnm : n ≤ m) {i : ℤ} (hi : i ∈ (C n).shape.active) :
      (C m).neck i = (C n).neck i := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact (hretain m i (hmonoAll hnm hi)).trans ih
  let A := ⋃ n, (C n).shape.active
  have hAnonempty : A.Nonempty := by
    obtain ⟨i, hi⟩ := (C 0).active_nonempty
    exact ⟨i, mem_iUnion.mpr ⟨0, hi⟩⟩
  have hcommon {i j : ℤ} (hi : i ∈ A) (hj : j ∈ A) :
      ∃ n, i ∈ (C n).shape.active ∧ j ∈ (C n).shape.active := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    obtain ⟨m, hm⟩ := mem_iUnion.mp hj
    exact ⟨max n m, hmonoAll (Nat.le_max_left _ _) hn,
      hmonoAll (Nat.le_max_right _ _) hm⟩
  have hAord : OrdConnected A := by
    constructor
    intro i hi j hj z hz
    obtain ⟨n, hni, hnj⟩ := hcommon hi hj
    have hiI : i ∈ Icc (a n) (b n) := by simpa only [hshape n, ChainShape.active] using hni
    have hjI : j ∈ Icc (a n) (b n) := by simpa only [hshape n, ChainShape.active] using hnj
    refine mem_iUnion.mpr ⟨n, ?_⟩
    simpa only [hshape n, ChainShape.active] using
      (show z ∈ Icc (a n) (b n) from ⟨hiI.1.trans hz.1, hz.2.trans hjI.2⟩)
  obtain ⟨shape, hactive⟩ := ChainShape.exists_active_eq_of_ordConnected A hAnonempty hAord
  let neck : ℤ → EpsilonNeck g := fun i =>
    if h : i ∈ A then (C (mem_iUnion.mp h).choose).neck i else (C 0).neck i
  have hneck (n : ℕ) (i : ℤ) (hi : i ∈ (C n).shape.active) : neck i = (C n).neck i := by
    have hA : i ∈ A := mem_iUnion.mpr ⟨n, hi⟩
    dsimp only [neck]
    rw [dif_pos hA]
    let k := (mem_iUnion.mp hA).choose
    have hk : i ∈ (C k).shape.active := (mem_iUnion.mp hA).choose_spec
    exact (hretainAll (Nat.le_max_left k n) hk).symm.trans
      (hretainAll (Nat.le_max_right k n) hi)
  let D : BalancedNeckChain g epsilon :=
    { shape := shape
      neck := neck
      source_necks := (C 0).source_necks
      selected := by
        intro i hi
        rw [hactive] at hi
        obtain ⟨n, hn⟩ := mem_iUnion.mp hi
        rw [hneck n i hn, ← hsource n]
        exact (C n).selected i hn
      active_nonempty := hactive ▸ hAnonempty
      epsilon_eq := by
        intro i hi
        rw [hactive] at hi
        obtain ⟨n, hn⟩ := mem_iUnion.mp hi
        rw [hneck n i hn]
        exact (C n).epsilon_eq i hn
      centers_distinct := by
        intro i hi j hj hij
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n j hnj]
        exact (C n).centers_distinct hni hnj hij
      adjacent_overlap := by
        intro i hi hj
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n (i + 1) hnj]
        exact (C n).adjacent_overlap i hni hnj
      overlap_contains_quarters := by
        intro i hi hj
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n (i + 1) hnj]
        exact (C n).overlap_contains_quarters i hni hnj
      overlap_within_three_quarters := by
        intro i hi hj
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n (i + 1) hnj]
        exact (C n).overlap_within_three_quarters i hni hnj
      later_disjoint_negative_end := by
        intro i hi j hj hij
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n j hnj]
        exact (C n).later_disjoint_negative_end i hni j hnj hij
      balanced_center_distance := by
        intro i hi hj
        rw [hactive] at hi hj
        obtain ⟨n, hni, hnj⟩ := hcommon hi hj
        rw [hneck n i hni, hneck n (i + 1) hnj]
        exact (C n).balanced_center_distance i hni hnj }
  exact ⟨D, hactive, rfl, hneck⟩

end PoincareConjecture.BalancedNeckChain
