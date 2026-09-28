import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEvent

set_option autoImplicit false

namespace PoincareConjecture.M25.Topology3D

inductive FamilySurgeryHistory (u : UnitTwoSphere) :
    {n : ℕ} → (Fin n → UnitTwoSphere × ℝ → E3) →
    {m : ℕ} → (Fin m → UnitTwoSphere × ℝ → E3) → Type
  | nil {n : ℕ} (psi : Fin n → UnitTwoSphere × ℝ → E3) :
      FamilySurgeryHistory u psi psi
  | cons {n m : ℕ} (psi : Fin n → UnitTwoSphere × ℝ → E3)
      (j : Fin n) (E : RegularSurgeryEvent (psi j) u)
      (e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2))
      (phi : Fin m → UnitTwoSphere × ℝ → E3)
      (tail : FamilySurgeryHistory u
        (fun a : Fin (n + 1) =>
          Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a))
        phi) :
      FamilySurgeryHistory u psi phi

def FamilySurgeryHistory.length
    {u : UnitTwoSphere} {n m : ℕ}
    {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {phi : Fin m → UnitTwoSphere × ℝ → E3} :
    FamilySurgeryHistory u psi phi → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ _ tail => tail.length + 1

theorem FamilySurgeryHistory.card_eq_length
    {u : UnitTwoSphere} {n m : ℕ}
    {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {phi : Fin m → UnitTwoSphere × ℝ → E3}
    (history : FamilySurgeryHistory u psi phi) :
    m = n + history.length := by
  induction history with
  | nil _ => rfl
  | cons _ _ _ _ _ tail ih =>
    change _ = _ + (tail.length + 1)
    omega

theorem FamilySurgeryHistory.fold
    {u : UnitTwoSphere}
    (P : (UnitTwoSphere × ℝ → E3) → Prop)
    (hstep : ∀ (parent : UnitTwoSphere × ℝ → E3)
      (E : RegularSurgeryEvent parent u),
      P (E.child 0) → P (E.child 1) → P parent)
    {n m : ℕ}
    {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {phi : Fin m → UnitTwoSphere × ℝ → E3}
    (history : FamilySurgeryHistory u psi phi)
    (hfinal : ∀ i : Fin m, P (phi i)) :
    ∀ i : Fin n, P (psi i) := by
  revert hfinal
  induction history with
  | nil _ => exact fun hfinal => hfinal
  | cons psi j E e _ _ ih =>
    intro hfinal i
    have hnext := ih hfinal
    by_cases hij : i = j
    · subst i
      apply hstep (psi j) E
      · simpa only [Equiv.apply_symm_apply, Sum.elim_inr] using
          hnext (e.symm (Sum.inr (0 : Fin 2)))
      · simpa only [Equiv.apply_symm_apply, Sum.elim_inr] using
          hnext (e.symm (Sum.inr (1 : Fin 2)))
    · simpa only [Equiv.apply_symm_apply, Sum.elim_inl] using
        hnext (e.symm (Sum.inl ⟨i, hij⟩))

end PoincareConjecture.M25.Topology3D
