import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.Scalar

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ)

theorem exists_descended_periodic (E : C(ℝ × ℝ, ℝ))
    (h₁ : ∀ x y, E (x + p, y) = E (x, y))
    (h₂ : ∀ x y, E (x, y + p) = E (x, y)) :
    ∃ e : C(AddCircle p × AddCircle p, ℝ), ∀ x, e (quotientMap p x) = E x := by
  classical
  have hrel (x y : ℝ × ℝ) (h : quotientMap p x = quotientMap p y) : E x = E y := by
    have hx : ((x.1 - y.1 : ℝ) : AddCircle p) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact congrArg Prod.fst h
    have hy : ((x.2 - y.2 : ℝ) : AddCircle p) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact congrArg Prod.snd h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff p).mp hx
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff p).mp hy
    have hx' : x.1 = y.1 + n • p := by linarith
    have hy' : x.2 = y.2 + m • p := by linarith
    have hp₁ : Function.Periodic (fun t => E (t, y.2 + m • p)) p :=
      fun t => h₁ t _
    have hp₂ : Function.Periodic (fun t => E (y.1, t)) p := fun t => h₂ _ t
    calc
      E x = E (y.1 + n • p, y.2 + m • p) := congrArg E (Prod.ext hx' hy')
      _ = E (y.1, y.2 + m • p) := hp₁.zsmul n y.1
      _ = E y := hp₂.zsmul m y.2
  let s := Function.surjInv (isOpenQuotientMap_quotientMap p).surjective
  let e : AddCircle p × AddCircle p → ℝ := E ∘ s
  have he (x : ℝ × ℝ) : e (quotientMap p x) = E x :=
    hrel _ x (Function.surjInv_eq _ _)
  have hc : Continuous e := by
    apply (isOpenQuotientMap_quotientMap p).isQuotientMap.continuous_iff.mpr
    have heq : e ∘ quotientMap p = E := funext he
    rw [heq]
    exact E.continuous
  exact ⟨⟨e, hc⟩, he⟩

theorem exists_scalar_decomposition (f : C(AddCircle p × AddCircle p, AddCircle p)) :
    ∃ (n m : ℤ) (e : C(AddCircle p × AddCircle p, ℝ)),
      ∀ z, f z = (e z : AddCircle p) + n • z.1 + m • z.2 := by
  obtain ⟨F, hF⟩ := exists_real_lift p f
  obtain ⟨n, m, hn, hm⟩ := exists_integer_periods p f F hF
  let E : C(ℝ × ℝ, ℝ) :=
    ⟨fun x => F x - n • x.1 - m • x.2, by fun_prop⟩
  have h₁ (x y : ℝ) : E (x + p, y) = E (x, y) := by
    change F (x + p, y) - n • (x + p) - m • y = F (x, y) - n • x - m • y
    rw [hn, smul_add]
    abel
  have h₂ (x y : ℝ) : E (x, y + p) = E (x, y) := by
    change F (x, y + p) - n • x - m • (y + p) = F (x, y) - n • x - m • y
    rw [hm, smul_add]
    abel
  obtain ⟨e, he⟩ := exists_descended_periodic p E h₁ h₂
  refine ⟨n, m, e, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := (isOpenQuotientMap_quotientMap p).surjective z
  rw [← hF, he]
  have h : F x = E x + n • x.1 + m • x.2 := by dsimp [E]; abel
  simpa only [quotientMap_apply, AddCircle.coe_add, AddCircle.coe_zsmul] using
    congrArg (fun t : ℝ => (t : AddCircle p)) h

end PoincareConjecture.M76.LinearTorus
