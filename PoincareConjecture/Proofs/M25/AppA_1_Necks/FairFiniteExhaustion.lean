import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteChainBackward
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.NeckOnlyCover

theorem exists_fair_finite_exhaustion :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ N ∈ H.necks, N.IsSeparating) →
      ∃ (a b : ℕ → ℤ) (C : ℕ → BalancedNeckChain g H.epsilon),
        a 0 = 0 ∧ b 0 = 0 ∧
        (∀ n, (C n).shape = ChainShape.finite (a n) (b n)) ∧
        (∀ n, (C n).source_necks = H.necks) ∧
        Antitone a ∧ Monotone b ∧
        (∀ n, ∀ i ∈ (C n).shape.active,
          (C (n + 1)).neck i = (C n).neck i) ∧
        (∀ n, ∀ i ∈ (C n).shape.active, ((C n).neck i).center ∈ H.X) ∧
        (∀ n, ∀ i ∈ (C n).shape.active, i + 1 ∈ (C n).shape.active →
          closure (((C n).neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
              ((C n).neck (i + 1)).carrier ∧
            closure (((C n).neck (i + 1)).region
                (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆
              ((C n).neck i).carrier) ∧
        (∀ n, ∀ i ∈ (C n).shape.active, i + 1 ∈ (C n).shape.active →
          (((C n).neck (i + 1)).center ∈
                closure (((C n).neck i).region 0 H.epsilon⁻¹) ∧
              ((C n).neck (i + 1)).center ∉ ((C n).neck i).carrier) ∨
            (((C n).neck i).center ∈
                closure (((C n).neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
              ((C n).neck i).center ∉ ((C n).neck (i + 1)).carrier)) ∧
        (∀ n, a (n + 1) = a n →
          H.X ∩ closure (((C n).neck (a n)).region (-H.epsilon⁻¹) 0) ⊆
            ⋃ i ∈ (C (n + 1)).shape.active, ((C (n + 1)).neck i).carrier) ∧
        (∀ n, b (n + 1) = b n →
          H.X ∩ closure (((C n).neck (b n)).region 0 H.epsilon⁻¹) ⊆
            ⋃ i ∈ (C (n + 1)).shape.active, ((C (n + 1)).neck i).carrier) := by
  classical
  obtain ⟨epsilonB, hB, hBcap, hbackward⟩ :=
    BalancedNeckChain.exists_finite_backward_extension_closed_quarters.{u}
  obtain ⟨epsilonF, hF, _, hforward⟩ :=
    BalancedNeckChain.exists_finite_forward_extension_closed_quarters.{u}
  refine ⟨min epsilonB epsilonF, lt_min hB hF, (min_le_left _ _).trans hBcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hsourceSep
  have heB : H.epsilon ≤ epsilonB := he.trans (min_le_left _ _)
  have heF : H.epsilon ≤ epsilonF := he.trans (min_le_right _ _)
  let U (C : BalancedNeckChain g H.epsilon) : Set M :=
    ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let Good (a b : ℤ) (C : BalancedNeckChain g H.epsilon) : Prop :=
    C.shape = ChainShape.finite a b ∧ C.source_necks = H.necks ∧
      (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) ⊆
            (C.neck (i + 1)).carrier ∧
          closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ⊆
            (C.neck i).carrier) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        ((C.neck (i + 1)).center ∈ closure ((C.neck i).region 0 H.epsilon⁻¹) ∧
            (C.neck (i + 1)).center ∉ (C.neck i).carrier) ∨
          ((C.neck i).center ∈
              closure ((C.neck (i + 1)).region (-H.epsilon⁻¹) 0) ∧
            (C.neck i).center ∉ (C.neck (i + 1)).carrier))
  have hactive {a b : ℤ} {C : BalancedNeckChain g H.epsilon}
      (hgood : Good a b C) (i : ℤ) : i ∈ C.shape.active ↔ a ≤ i ∧ i ≤ b := by
    rw [hgood.1]
    rfl
  have hbounds {a b : ℤ} {C : BalancedNeckChain g H.epsilon}
      (hgood : Good a b C) : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive hgood i).mp hi).1.trans ((hactive hgood i).mp hi).2
  have hsep {a b : ℤ} {C : BalancedNeckChain g H.epsilon}
      (hgood : Good a b C) : ∀ i ∈ C.shape.active, (C.neck i).IsSeparating := by
    intro i hi
    obtain ⟨N, hN, hselected⟩ := C.selected i hi
    rw [hgood.2.1] at hN
    unfold EpsilonNeck.IsSeparating
    rw [hselected.2.2.1, hselected.2.2.2.2.1]
    exact hsourceSep N hN
  have hunion {C D : BalancedNeckChain g H.epsilon}
      (hinc : C.shape.active ⊆ D.shape.active)
      (hretain : ∀ i ∈ C.shape.active, D.neck i = C.neck i) : U C ⊆ U D := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hinc hi, by simpa only [hretain i hi] using hx⟩
  have hnegative (a b : ℤ) (C : BalancedNeckChain g H.epsilon)
      (hgood : Good a b C) :
      ∃ (a' : ℤ) (D : BalancedNeckChain g H.epsilon),
        Good a' b D ∧ a' ≤ a ∧
          (∀ i ∈ C.shape.active, D.neck i = C.neck i) ∧
          (a' = a → H.X ∩ closure ((C.neck a).region (-H.epsilon⁻¹) 0) ⊆ U D) := by
    by_cases hgrow : ∃ y ∈ H.X,
        y ∈ closure ((C.neck a).region (-H.epsilon⁻¹) 0) ∧ y ∉ U C
    · obtain ⟨y, hyX, hy, hyout⟩ := hgrow
      obtain ⟨N', hN', hNc⟩ := H.pointwise_center_cover y hyX
      obtain ⟨R, D, _, hselected, hDshape, hDsource, hDneck, hDquarters⟩ :=
        hbackward C hgood.1 heB (hsep hgood) hgood.2.2.2.1 N'
          (by rw [hgood.2.1]; exact hN') (H.neck_epsilon N' hN')
          (by simpa only [hNc] using hy) (by simpa only [hNc] using hyout)
      have hab : a ≤ b := hbounds hgood
      have ha : a ∈ C.shape.active := (hactive hgood a).mpr ⟨le_rfl, hab⟩
      have hRc : R.center = y := hselected.2.2.1.trans hNc
      have hDnew : D.neck (a - 1) = R := by rw [hDneck, Function.update_self]
      have hDold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
        have hia := ((hactive hgood i).mp hi).1
        have hne : i ≠ a - 1 := by omega
        rw [hDneck, Function.update_of_ne hne]
      have hDgood : Good (a - 1) b D := by
        refine ⟨hDshape, hDsource.trans hgood.2.1, ?_, hDquarters, ?_⟩
        · intro i hi
          rw [hDshape] at hi
          change a - 1 ≤ i ∧ i ≤ b at hi
          by_cases hie : i = a - 1
          · simpa only [hie, hDnew, hRc] using hyX
          · have hio : i ∈ C.shape.active := (hactive hgood i).mpr ⟨by omega, hi.2⟩
            rw [hDold i hio]
            exact hgood.2.2.1 i hio
        · intro i hi hi1
          rw [hDshape] at hi hi1
          change a - 1 ≤ i ∧ i ≤ b at hi
          change a - 1 ≤ i + 1 ∧ i + 1 ≤ b at hi1
          by_cases hie : i = a - 1
          · rw [hie, show a - 1 + 1 = a by omega, hDnew, hDold a ha, hRc]
            exact Or.inr ⟨hy, fun hx => hyout (mem_iUnion₂.mpr ⟨a, ha, hx⟩)⟩
          · have hio : i ∈ C.shape.active := (hactive hgood i).mpr ⟨by omega, hi.2⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (hactive hgood _).mpr ⟨by omega, hi1.2⟩
            rw [hDold i hio, hDold (i + 1) hi1o]
            exact hgood.2.2.2.2 i hio hi1o
      refine ⟨a - 1, D, hDgood, by omega, hDold, ?_⟩
      intro heq
      have hfalse : False := by omega
      exact hfalse.elim
    · refine ⟨a, C, hgood, le_rfl, fun _ _ => rfl, ?_⟩
      intro _ x hx
      by_contra hnot
      exact hgrow ⟨x, hx.1, hx.2, hnot⟩
  have hpositive (a b : ℤ) (C : BalancedNeckChain g H.epsilon)
      (hgood : Good a b C) :
      ∃ (b' : ℤ) (D : BalancedNeckChain g H.epsilon),
        Good a b' D ∧ b ≤ b' ∧
          (∀ i ∈ C.shape.active, D.neck i = C.neck i) ∧
          (b' = b → H.X ∩ closure ((C.neck b).region 0 H.epsilon⁻¹) ⊆ U D) := by
    by_cases hgrow : ∃ y ∈ H.X,
        y ∈ closure ((C.neck b).region 0 H.epsilon⁻¹) ∧ y ∉ U C
    · obtain ⟨y, hyX, hy, hyout⟩ := hgrow
      obtain ⟨N', hN', hNc⟩ := H.pointwise_center_cover y hyX
      obtain ⟨R, D, _, hselected, hDshape, hDsource, hDneck, hDquarters⟩ :=
        hforward C hgood.1 heF (hsep hgood) hgood.2.2.2.1 N'
          (by rw [hgood.2.1]; exact hN') (H.neck_epsilon N' hN')
          (by simpa only [hNc] using hy) (by simpa only [hNc] using hyout)
      have hab : a ≤ b := hbounds hgood
      have hb : b ∈ C.shape.active := (hactive hgood b).mpr ⟨hab, le_rfl⟩
      have hRc : R.center = y := hselected.2.2.1.trans hNc
      have hDnew : D.neck (b + 1) = R := by rw [hDneck, Function.update_self]
      have hDold (i : ℤ) (hi : i ∈ C.shape.active) : D.neck i = C.neck i := by
        have hib := ((hactive hgood i).mp hi).2
        have hne : i ≠ b + 1 := by omega
        rw [hDneck, Function.update_of_ne hne]
      have hDgood : Good a (b + 1) D := by
        refine ⟨hDshape, hDsource.trans hgood.2.1, ?_, hDquarters, ?_⟩
        · intro i hi
          rw [hDshape] at hi
          change a ≤ i ∧ i ≤ b + 1 at hi
          by_cases hie : i = b + 1
          · simpa only [hie, hDnew, hRc] using hyX
          · have hio : i ∈ C.shape.active := (hactive hgood i).mpr ⟨hi.1, by omega⟩
            rw [hDold i hio]
            exact hgood.2.2.1 i hio
        · intro i hi hi1
          rw [hDshape] at hi hi1
          change a ≤ i ∧ i ≤ b + 1 at hi
          change a ≤ i + 1 ∧ i + 1 ≤ b + 1 at hi1
          by_cases hie : i = b
          · rw [hie, hDold b hb, hDnew, hRc]
            exact Or.inl ⟨hy, fun hx => hyout (mem_iUnion₂.mpr ⟨b, hb, hx⟩)⟩
          · have hio : i ∈ C.shape.active := (hactive hgood i).mpr ⟨hi.1, by omega⟩
            have hi1o : i + 1 ∈ C.shape.active :=
              (hactive hgood _).mpr ⟨hi1.1, by omega⟩
            rw [hDold i hio, hDold (i + 1) hi1o]
            exact hgood.2.2.2.2 i hio hi1o
      refine ⟨b + 1, D, hDgood, by omega, hDold, ?_⟩
      intro heq
      have hfalse : False := by omega
      exact hfalse.elim
    · refine ⟨b, C, hgood, le_rfl, fun _ _ => rfl, ?_⟩
      intro _ x hx
      by_contra hnot
      exact hgrow ⟨x, hx.1, hx.2, hnot⟩
  let State := {s : ℤ × ℤ × BalancedNeckChain g H.epsilon // Good s.1 s.2.1 s.2.2}
  let Step (s t : State) : Prop :=
    t.1.1 ≤ s.1.1 ∧ s.1.2.1 ≤ t.1.2.1 ∧
      (∀ i ∈ s.1.2.2.shape.active, t.1.2.2.neck i = s.1.2.2.neck i) ∧
      (t.1.1 = s.1.1 → H.X ∩
        closure ((s.1.2.2.neck s.1.1).region (-H.epsilon⁻¹) 0) ⊆ U t.1.2.2) ∧
      (t.1.2.1 = s.1.2.1 → H.X ∩
        closure ((s.1.2.2.neck s.1.2.1).region 0 H.epsilon⁻¹) ⊆ U t.1.2.2)
  have hround (s : State) : ∃ t : State, Step s t := by
    obtain ⟨a', P, hP, ha', hPC, hneg⟩ := hnegative s.1.1 s.1.2.1 s.1.2.2 s.2
    obtain ⟨b', D, hD, hb', hDP, hpos⟩ := hpositive a' s.1.2.1 P hP
    have hCP : s.1.2.2.shape.active ⊆ P.shape.active := by
      intro i hi
      have hii := (hactive s.2 i).mp hi
      exact (hactive hP i).mpr ⟨ha'.trans hii.1, hii.2⟩
    have hPD : P.shape.active ⊆ D.shape.active := by
      intro i hi
      have hii := (hactive hP i).mp hi
      exact (hactive hD i).mpr ⟨hii.1, hii.2.trans hb'⟩
    have hPU : U P ⊆ U D := hunion hPD hDP
    refine ⟨⟨(a', b', D), hD⟩, ha', hb', ?_, ?_, ?_⟩
    · intro i hi
      exact (hDP i (hCP hi)).trans (hPC i hi)
    · intro heq x hx
      exact hPU (hneg heq hx)
    · intro heq x hx
      have hb : s.1.2.1 ∈ s.1.2.2.shape.active :=
        (hactive s.2 _).mpr ⟨hbounds s.2, le_rfl⟩
      apply hpos heq
      simpa only [hPC _ hb] using hx
  obtain ⟨x0, hx0⟩ := H.connected_X.nonempty
  obtain ⟨N0, hN0, hN0c⟩ := H.pointwise_center_cover x0 hx0
  have hsingle {i : ℤ} (hi : i ∈ (ChainShape.finite 0 0).active)
      (hi1 : i + 1 ∈ (ChainShape.finite 0 0).active) : False := by
    change 0 ≤ i ∧ i ≤ 0 at hi
    change 0 ≤ i + 1 ∧ i + 1 ≤ 0 at hi1
    omega
  let C0 : BalancedNeckChain g H.epsilon := {
    shape := .finite 0 0
    neck := fun _ => N0
    source_necks := H.necks
    selected := by
      intro _ _
      refine ⟨N0, hN0, rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
      intro z _
      simp only [one_mul]
    active_nonempty := ⟨0, le_rfl, le_rfl⟩
    epsilon_eq := fun _ _ => H.neck_epsilon N0 hN0
    centers_distinct := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    adjacent_overlap := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_contains_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    overlap_within_three_quarters := fun _ hi hi1 => (hsingle hi hi1).elim
    later_disjoint_negative_end := by
      intro i hi j hj hij
      change 0 ≤ i ∧ i ≤ 0 at hi
      change 0 ≤ j ∧ j ≤ 0 at hj
      omega
    balanced_center_distance := fun _ hi hi1 => (hsingle hi hi1).elim }
  have hC0 : Good 0 0 C0 := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · intro i _
      change N0.center ∈ H.X
      simpa only [hN0c] using hx0
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
    · intro _ hi hi1
      exact (hsingle hi hi1).elim
  let seed : State := ⟨(0, 0, C0), hC0⟩
  choose step hstep using hround
  let S : ℕ → State := fun n => step^[n] seed
  have hsucc (n : ℕ) : S (n + 1) = step (S n) :=
    Function.iterate_succ_apply' step n seed
  have hS (n : ℕ) : Step (S n) (S (n + 1)) := by
    rw [hsucc]
    exact hstep (S n)
  refine ⟨fun n => (S n).1.1, fun n => (S n).1.2.1, fun n => (S n).1.2.2,
    rfl, rfl, fun n => (S n).2.1, fun n => (S n).2.2.1,
    antitone_nat_of_succ_le (fun n => (hS n).1),
    monotone_nat_of_le_succ (fun n => (hS n).2.1),
    fun n => (hS n).2.2.1, fun n => (S n).2.2.2.1,
    fun n => (S n).2.2.2.2.1, fun n => (S n).2.2.2.2.2,
    fun n => (hS n).2.2.2.1, fun n => (hS n).2.2.2.2⟩

end PoincareConjecture.NeckOnlyCover
