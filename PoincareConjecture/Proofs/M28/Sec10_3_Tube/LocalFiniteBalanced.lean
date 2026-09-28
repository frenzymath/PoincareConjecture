import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.InitialEnd
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFiniteList
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union
import Mathlib.Data.List.ChainOfFn












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain



theorem exists_finite_cylinder_with_middle_threshold_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          RoundCylinderSpace C.unionOpen ∞,
          ∃ i ∈ C.shape.active, ∃ c ∈ Ioo (-ε⁻¹) ε⁻¹,
            range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
              range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, c)) := by
  obtain ⟨ε₀, hε₀, hε₀small, hfinite⟩ :=
    EpsilonNeck.exists_finite_neck_cylinder_with_middle_m28.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape
  classical
  have hactive : C.shape.active = Icc a b := by rw [hshape]; rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    rw [hactive] at hi
    exact hi.1.trans hi.2
  have ha : a ∈ C.shape.active := hactive.symm ▸ ⟨le_rfl, hab⟩
  have hea := C.epsilon_eq a ha
  have hepos : 0 < ε := hea ▸ (C.neck a).epsilon_pos
  have hinv := inv_pos.mpr hepos
  let n := (b - a).toNat
  have hn : (n : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  let xs : List (EpsilonNeck g) :=
    List.ofFn fun i : Fin n => C.neck (a + (i.val : ℤ) + 1)
  have hindex (i : Fin (n + 1)) : a + (i.val : ℤ) ∈ C.shape.active := by
    rw [hactive]
    have hi := i.isLt
    constructor <;> omega
  have htailindex (i : Fin n) : a + (i.val : ℤ) + 1 ∈ C.shape.active := by
    rw [hactive]
    have hi := i.isLt
    constructor <;> omega
  have hlist : C.neck a :: xs = List.ofFn (fun i : Fin (n + 1) =>
      C.neck (a + (i.val : ℤ))) := by
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Int.natCast_zero, add_zero, Fin.val_succ,
      Int.natCast_add, Int.natCast_one, ← add_assoc]
    rfl
  have hsmall : ∀ N ∈ C.neck a :: xs, N.epsilon ≤ ε₀ := by
    intro N hN
    rw [hlist] at hN
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
    rw [C.epsilon_eq _ (hindex i)]
    exact hε
  have hchain : List.IsChain (fun A B : EpsilonNeck g =>
      (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
      A.carrier ∩ B.carrier ⊆ A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
        B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (C.neck a :: xs) := by
    rw [hlist, List.isChain_ofFn]
    intro i hi
    have hj : a + (i : ℤ) ∈ C.shape.active := hindex ⟨i, by omega⟩
    have hj' : a + (i : ℤ) + 1 ∈ C.shape.active := by
      rw [hactive]
      constructor <;> omega
    have he := C.epsilon_eq _ hj
    have he' := C.epsilon_eq _ hj'
    simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc, he, he'] using
      And.intro (C.overlap_contains_quarters _ hj hj').2
        (C.overlap_within_three_quarters _ hj hj')
  let J := (Finset.univ : Finset (Fin n)).image fun i => a + (i.val : ℤ) + 1
  have hJ : ∀ j ∈ J, j ∈ C.shape.active ∧ a < j := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨htailindex i, by omega⟩
  let cut := -(3 / 4 : ℝ) * ε⁻¹
  have hcut : cut ∈ Ioo (-ε⁻¹) ε⁻¹ := by dsimp [cut]; constructor <;> linarith
  have hcutq : cut < -ε⁻¹ / 2 := by dsimp [cut]; linarith
  obtain ⟨c, hc, havoid⟩ := C.exists_common_negative_end_cut ha J hJ hcut.1
  have hcdom : c ∈ Ioo (-(C.neck a).epsilon⁻¹) (C.neck a).epsilon⁻¹ := by
    rw [hea]
    exact ⟨hc.1, hc.2.trans hcut.2⟩
  have havoid' : ∀ B ∈ xs,
      Disjoint B.carrier ((C.neck a).region (-(C.neck a).epsilon⁻¹) c) := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    rw [hea]
    exact havoid _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨D, N, s, hN, hs, hDzero, _, _⟩ := hfinite (C.neck a) xs hsmall c cut hcdom
    (by simpa only [hea] using hcut) hc.2 (by simpa only [hea] using hcutq) hchain havoid'
  have hUnion : EpsilonNeck.finiteNeckUnion_m28 (C.neck a :: xs) = C.unionOpen := by
    apply SetLike.coe_injective
    rw [EpsilonNeck.finiteNeckUnion_carrier_m28]
    ext x
    constructor
    · intro hx
      obtain ⟨N, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hN, hx⟩ := mem_iUnion.mp hx
      rw [hlist] at hN
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
      exact mem_iUnion.mpr ⟨⟨a + (i.val : ℤ), hindex i⟩, hx⟩
    · intro hx
      obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      have hj : a ≤ j.1 ∧ j.1 ≤ b := by simpa only [hactive, mem_Icc] using j.2
      let i : Fin (n + 1) := ⟨(j.1 - a).toNat, by omega⟩
      have heq : a + (i.val : ℤ) = j.1 := by dsimp [i]; omega
      refine mem_iUnion.mpr ⟨C.neck j.1, mem_iUnion.mpr ⟨?_, hx⟩⟩
      rw [hlist]
      exact List.mem_ofFn.mpr ⟨i, congrArg C.neck heq⟩
  rw [hlist] at hN
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
  have hout : ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace (EpsilonNeck.finiteNeckUnion_m28 (C.neck a :: xs)) ∞,
      ∃ i ∈ C.shape.active, ∃ c ∈ Ioo (-ε⁻¹) ε⁻¹,
        range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
          range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, c)) := by
    refine ⟨D, a + (i.val : ℤ), hindex i, s, ?_, hDzero⟩
    simpa only [C.epsilon_eq _ (hindex i)] using hs
  exact hUnion ▸ hout



theorem exists_finite_cylinder_threshold_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ a b : ℤ, C.shape = .finite a b →
        Nonempty (Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          RoundCylinderSpace C.unionOpen ∞) := by
  obtain ⟨ε₀, hε₀, hsmall, h⟩ := exists_finite_cylinder_with_middle_threshold_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε a b hshape
  obtain ⟨D, _⟩ := h C hε a b hshape
  exact ⟨D⟩

end PoincareConjecture.BalancedNeckChain
