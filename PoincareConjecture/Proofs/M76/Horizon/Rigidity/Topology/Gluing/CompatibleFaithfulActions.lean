import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.End

set_option autoImplicit false

namespace PoincareConjecture.M76

namespace IncompressibleGluing

universe u v

variable {H G : Type u} [Group H] [Group G]

private theorem rightCoset_mul (f : H →* G) (h : H) (g : G) :
    (Quotient.mk'' (f h * g) : Quotient (QuotientGroup.rightRel f.range)) =
      Quotient.mk'' g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have heq : g * (f h * g)⁻¹ = f h⁻¹ := by
    simp [mul_inv_rev]
  rw [heq]
  exact ⟨h⁻¹, rfl⟩

private theorem rightCosetCoordinate_bijective (f : H →* G)
    (hf : Function.Injective f) :
    Function.Bijective
      (fun p : H × Quotient (QuotientGroup.rightRel f.range) => f p.1 * p.2.out) := by
  constructor
  · rintro ⟨h, q⟩ ⟨h', q'⟩ heq
    have hq : q = q' := by
      have := congrArg (fun g : G =>
        (Quotient.mk'' g : Quotient (QuotientGroup.rightRel f.range))) heq
      simpa only [rightCoset_mul, Quotient.out_eq'] using this
    subst q'
    exact Prod.ext (hf (mul_right_cancel heq)) rfl
  · intro g
    let q : Quotient (QuotientGroup.rightRel f.range) := Quotient.mk'' g
    have hmem : g * q.out⁻¹ ∈ f.range := by
      exact QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq' q))
    obtain ⟨h, hh⟩ := hmem
    refine ⟨(h, q), ?_⟩
    change f h * q.out = g
    rw [hh]
    simp [mul_assoc]

private noncomputable def rightCosetCoordinate (f : H →* G)
    (hf : Function.Injective f) :
    H × Quotient (QuotientGroup.rightRel f.range) ≃ G :=
  Equiv.ofBijective _ (rightCosetCoordinate_bijective f hf)

private theorem rightCosetCoordinate_mul (f : H →* G)
    (hf : Function.Injective f) (h : H)
    (p : H × Quotient (QuotientGroup.rightRel f.range)) :
    rightCosetCoordinate f hf (h * p.1, p.2) =
      f h * rightCosetCoordinate f hf p := by
  change f (h * p.1) * p.2.out = f h * (f p.1 * p.2.out)
  rw [map_mul, mul_assoc]

def regularProduct (G : Type u) [Group G] (K : Type v) :
    G →* Equiv.Perm (G × K) where
  toFun g := Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl K)
  map_one' := by ext p <;> simp
  map_mul' g h := by ext p <;> simp [mul_assoc]

theorem regularProduct_injective (K : Type v) [Nonempty K] :
    Function.Injective (regularProduct G K) := by
  intro g h heq
  obtain ⟨k⟩ := ‹Nonempty K›
  have := congrArg (fun e : Equiv.Perm (G × K) => (e (1, k)).1) heq
  simpa [regularProduct] using this

private def exchangeCoordinates {A B C : Type u} :
    (A × B) × (A × C) ≃ (A × C) × (A × B) where
  toFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  invFun p := ((p.1.1, p.2.2), (p.2.1, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_regular_action_exchange {J : Type u} [Group J]
    (f : H →* G) (g : H →* J)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ c : Equiv.Perm (G × J), ∀ h (p : G × J),
      c (f h * p.1, p.2) = ((c p).1, g h * (c p).2) := by
  classical
  let Q₀ := Quotient (QuotientGroup.rightRel f.range)
  let Q₁ := Quotient (QuotientGroup.rightRel g.range)
  let e₀ : H × Q₀ ≃ G := rightCosetCoordinate f hf
  let e₁ : H × Q₁ ≃ J := rightCosetCoordinate g hg
  let E : (H × Q₀) × (H × Q₁) ≃ G × J := Equiv.prodCongr e₀ e₁
  let c : Equiv.Perm (G × J) := E.symm.trans
    (exchangeCoordinates.trans
      ((Equiv.prodCongr e₁ e₀).trans (Equiv.prodComm J G)))
  refine ⟨c, ?_⟩
  intro h p
  have he₀ : e₀.symm (f h * p.1) =
      (h * (e₀.symm p.1).1, (e₀.symm p.1).2) := by
    apply e₀.injective
    rw [e₀.apply_symm_apply, rightCosetCoordinate_mul,
      show rightCosetCoordinate f hf (e₀.symm p.1) = p.1 from e₀.apply_symm_apply _]
  change (e₀ ((e₁.symm p.2).1, (e₀.symm (f h * p.1)).2),
      e₁ ((e₀.symm (f h * p.1)).1, (e₁.symm p.2).2)) =
    (e₀ ((e₁.symm p.2).1, (e₀.symm p.1).2),
      g h * e₁ ((e₀.symm p.1).1, (e₁.symm p.2).2))
  rw [he₀]
  exact Prod.ext rfl
    (rightCosetCoordinate_mul g hg h ((e₀.symm p.1).1, (e₁.symm p.2).2))

theorem exists_compatible_faithful_actions {J : Type u} [Group J]
    (f : H →* G) (g : H →* J)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (a : G →* Equiv.Perm (G × J)) (b : J →* Equiv.Perm (G × J)),
      Function.Injective a ∧ Function.Injective b ∧ a.comp f = b.comp g := by
  classical
  let Q₀ := Quotient (QuotientGroup.rightRel f.range)
  let Q₁ := Quotient (QuotientGroup.rightRel g.range)
  let : Nonempty Q₀ := ⟨Quotient.mk'' (1 : G)⟩
  let : Nonempty Q₁ := ⟨Quotient.mk'' (1 : J)⟩
  let Ω := (H × Q₀) × (H × Q₁)
  let e₀ : H × Q₀ ≃ G := rightCosetCoordinate f hf
  let e₁ : H × Q₁ ≃ J := rightCosetCoordinate g hg
  let d₀ : Ω ≃ G × (H × Q₁) := Equiv.prodCongr e₀ (Equiv.refl _)
  let d₁ : Ω ≃ J × (H × Q₀) :=
    exchangeCoordinates.trans (Equiv.prodCongr e₁ (Equiv.refl _))
  let a₀ : G →* Equiv.Perm Ω :=
    d₀.symm.permCongrHom.toMonoidHom.comp (regularProduct G (H × Q₁))
  let a₁ : J →* Equiv.Perm Ω :=
    d₁.symm.permCongrHom.toMonoidHom.comp (regularProduct J (H × Q₀))
  have h₀ : Function.Injective a₀ :=
    d₀.symm.permCongrHom.injective.comp (regularProduct_injective _)
  have h₁ : Function.Injective a₁ :=
    d₁.symm.permCongrHom.injective.comp (regularProduct_injective _)
  have hcompat : a₀.comp f = a₁.comp g := by
    apply MonoidHom.ext
    intro h
    apply Equiv.ext
    intro p
    have hc₀ : e₀.symm (f h * e₀ p.1) = (h * p.1.1, p.1.2) := by
      apply e₀.injective
      rw [e₀.apply_symm_apply]
      exact (rightCosetCoordinate_mul f hf h p.1).symm
    have hc₁ : e₁.symm (g h * e₁ (p.1.1, p.2.2)) =
        (h * p.1.1, p.2.2) := by
      apply e₁.injective
      rw [e₁.apply_symm_apply]
      exact (rightCosetCoordinate_mul g hg h (p.1.1, p.2.2)).symm
    change (e₀.symm (f h * e₀ p.1), p.2) =
      (((e₁.symm (g h * e₁ (p.1.1, p.2.2))).1, p.1.2),
        (p.2.1, (e₁.symm (g h * e₁ (p.1.1, p.2.2))).2))
    rw [hc₀, hc₁]
  let E : Ω ≃ G × J := Equiv.prodCongr e₀ e₁
  refine ⟨E.permCongrHom.toMonoidHom.comp a₀,
    E.permCongrHom.toMonoidHom.comp a₁,
    E.permCongrHom.injective.comp h₀,
    E.permCongrHom.injective.comp h₁, ?_⟩
  exact congrArg (fun c : H →* Equiv.Perm Ω =>
    E.permCongrHom.toMonoidHom.comp c) hcompat

end IncompressibleGluing

end PoincareConjecture.M76
