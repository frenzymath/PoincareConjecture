import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RelativeSuccessorHeight
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicFiniteChain
import Mathlib.Data.Int.Init










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem BalancedNeckChain.exists_finite_relative_saturated_heights :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ {epsilon : ℝ} (C : BalancedNeckChain g epsilon) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
        let L := epsilon⁻¹
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        ∃ F : ℤ → M → ℝ,
          ∀ i ∈ C.shape.active,
            ContinuousOn (F i) U ∧
            (∀ x ∈ (C.neck i).carrier,
              F i x = ((C.neck i).coordinate_inverse x).2) ∧
            (∀ x ∈ U, x ∉ (C.neck i).carrier →
              F i x = -L ∨ F i x = L) := by
  obtain ⟨epsilon0, hpos, hcap, hsuccessor⟩ :=
    EpsilonNeck.exists_relative_successor_height_continuity.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a b hshape heps
  classical
  let L := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let P : ℤ → Prop := fun i => ∃ F : M → ℝ,
    ContinuousOn F U ∧
    (∀ x ∈ (C.neck i).carrier, F x = ((C.neck i).coordinate_inverse x).2) ∧
    (∀ x ∈ U, x ∉ (C.neck i).carrier → F x = -L ∨ F x = L)
  change ∃ F : ℤ → M → ℝ, ∀ i ∈ C.shape.active,
    ContinuousOn (F i) U ∧
    (∀ x ∈ (C.neck i).carrier, F i x = ((C.neck i).coordinate_inverse x).2) ∧
    (∀ x ∈ U, x ∉ (C.neck i).carrier → F i x = -L ∨ F i x = L)
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hNU (i : ℤ) (hi : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hbase : P a := by
    refine ⟨fun x => if x ∈ (C.neck a).carrier then
      ((C.neck a).coordinate_inverse x).2 else L, ?_, ?_, ?_⟩
    · exact (C.continuousOn_initial_height_of_finite hshape).1
    · intro x hx
      simp only [if_pos hx]
    · intro x _ hx
      exact Or.inr (if_neg hx)
  have hadvance (i : ℤ) (hi : i ∈ C.shape.active)
      (hn : i + 1 ∈ C.shape.active) (h : P i) : P (i + 1) := by
    obtain ⟨F, hFc, hFin, hFout⟩ := h
    have hei := C.epsilon_eq i hi
    have hen := C.epsilon_eq (i + 1) hn
    have hNi : (C.neck i).epsilon ≤ epsilon0 := by
      rw [hei]
      exact heps
    have hquarter :
        (C.neck i).region ((C.neck i).epsilon⁻¹ / 2) (C.neck i).epsilon⁻¹ ⊆
          (C.neck (i + 1)).carrier := by
      simpa only [hei] using (C.overlap_contains_quarters i hi hn).1
    have hoverlap : (C.neck i).carrier ∩ (C.neck (i + 1)).carrier ⊆
        (C.neck i).region (-(C.neck i).epsilon⁻¹ / 2) (C.neck i).epsilon⁻¹ ∩
          (C.neck (i + 1)).region (-(C.neck i).epsilon⁻¹)
            ((C.neck i).epsilon⁻¹ / 2) := by
      simpa only [hei] using C.overlap_within_three_quarters i hi hn
    let G : M → ℝ := fun x => if x ∈ (C.neck (i + 1)).carrier then
      ((C.neck (i + 1)).coordinate_inverse x).2
      else if F x < 3 * L / 4 then -L else L
    refine ⟨G, ?_, ?_, ?_⟩
    · have hc := hsuccessor (C.neck i) (C.neck (i + 1)) hNi
        (hen.trans hei.symm) hquarter hoverlap U (hNU i hi) (hNU (i + 1) hn)
        F hFc hFin (by simpa only [hei] using hFout)
      simpa only [G, L, hei] using hc
    · intro x hx
      simp only [G, if_pos hx]
    · intro x _ hx
      dsimp only [G]
      rw [if_neg hx]
      by_cases hf : F x < 3 * L / 4
      · exact Or.inl (if_pos hf)
      · exact Or.inr (if_neg hf)
  have hexists (i : ℤ) (hi : i ∈ C.shape.active) : P i := by
    have hiab := (hactive i).mp hi
    refine Int.leInduction (m := a) (motive := fun j _ => j ≤ b → P j)
      (fun _ => hbase) ?_ i hiab.1 hiab.2
    intro j haj ih hjb
    have hj : j ∈ C.shape.active := (hactive j).mpr ⟨haj, by omega⟩
    have hjn : j + 1 ∈ C.shape.active := (hactive (j + 1)).mpr ⟨by omega, hjb⟩
    exact hadvance j hj hjn (ih (by omega))
  refine ⟨fun i => if hi : i ∈ C.shape.active then
    (hexists i hi).choose else fun _ => 0, ?_⟩
  intro i hi
  simpa only [dif_pos hi] using (hexists i hi).choose_spec

end PoincareConjecture
