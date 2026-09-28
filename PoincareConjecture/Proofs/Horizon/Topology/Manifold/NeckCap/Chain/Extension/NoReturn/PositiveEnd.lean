import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.List
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.InitialEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import Mathlib.Data.List.ChainOfFn

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_positive_end_exclusion_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
          Disjoint (C.neck i).carrier ((C.neck j).region (ε⁻¹ / 2) ε⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, hfinite⟩ := EpsilonNeck.exists_finite_neck_cylinder_with_middle.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε i hi j hj hij
  classical
  have hei := C.epsilon_eq i hi
  have hej := C.epsilon_eq j hj
  have hepos : 0 < ε := hei ▸ (C.neck i).epsilon_pos
  have hinv := inv_pos.mpr hepos
  let n := (j - i).toNat
  have hn : (n : ℤ) = j - i := Int.toNat_of_nonneg (by omega)
  let xs : List (EpsilonNeck g) :=
    List.ofFn fun k : Fin n => C.neck (i + (k.val : ℤ) + 1)
  have hindex (k : Fin (n + 1)) : i + (k.val : ℤ) ∈ C.shape.active :=
    C.shape.ordConnected_active.out hi hj ⟨by omega, by have hk := k.isLt; omega⟩
  have htailindex (k : Fin n) : i + (k.val : ℤ) + 1 ∈ C.shape.active :=
    C.shape.ordConnected_active.out hi hj ⟨by omega, by have hk := k.isLt; omega⟩
  have hlist : C.neck i :: xs = List.ofFn (fun k : Fin (n + 1) =>
      C.neck (i + (k.val : ℤ))) := by
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Int.natCast_zero, add_zero, Fin.val_succ,
      Int.natCast_add, Int.natCast_one, ← add_assoc]
    rfl
  have hsmall : ∀ N ∈ C.neck i :: xs, N.epsilon ≤ ε₀ := by
    intro N hN
    rw [hlist] at hN
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hN
    rw [C.epsilon_eq _ (hindex k)]
    exact hε
  have hchain : List.IsChain (fun A B : EpsilonNeck g =>
      (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
      A.carrier ∩ B.carrier ⊆ A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
        B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (C.neck i :: xs) := by
    rw [hlist, List.isChain_ofFn]
    intro k hk
    have hki : i + (k : ℤ) ∈ C.shape.active := hindex ⟨k, by omega⟩
    have hk' : i + (k : ℤ) + 1 ∈ C.shape.active := htailindex ⟨k, by omega⟩
    have he := C.epsilon_eq _ hki
    have he' := C.epsilon_eq _ hk'
    simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc, he, he'] using
      And.intro (C.overlap_contains_quarters _ hki hk').2
        (C.overlap_within_three_quarters _ hki hk')
  let J := (Finset.univ : Finset (Fin n)).image fun k => i + (k.val : ℤ) + 1
  have hJ : ∀ k ∈ J, k ∈ C.shape.active ∧ i < k := by
    intro k hk
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨htailindex l, by omega⟩
  let cut := -(3 / 4 : ℝ) * ε⁻¹
  have hcut : cut ∈ Ioo (-ε⁻¹) ε⁻¹ := by dsimp [cut]; constructor <;> linarith
  have hcutq : cut < -ε⁻¹ / 2 := by dsimp [cut]; linarith
  obtain ⟨c, hc, havoid⟩ := C.exists_common_negative_end_cut hi J hJ hcut.1
  have hcdom : c ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
    rw [hei]
    exact ⟨hc.1, hc.2.trans hcut.2⟩
  have havoid' : ∀ B ∈ xs,
      Disjoint B.carrier ((C.neck i).region (-(C.neck i).epsilon⁻¹) c) := by
    intro B hB
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hB
    rw [hei]
    exact havoid _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  obtain ⟨_, N, _, _, _, _, hlast, hexclude⟩ := hfinite (C.neck i) xs hsmall c cut hcdom
    (by simpa only [hei] using hcut) hc.2 (by simpa only [hei] using hcutq) hchain havoid'
  have hN : N = C.neck j := by
    simp only [hlist, List.getLast_ofFn_succ] at hlast
    have heq : i + (n : ℤ) = j := by omega
    simpa only [Fin.val_last, heq] using hlast
  have hxs : xs ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [xs, List.length_ofFn, List.length_nil] at hlen
    omega
  simpa only [hN, hej] using hexclude hxs

end PoincareConjecture.BalancedNeckChain
