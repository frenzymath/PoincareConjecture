import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.AntipodalCoverHomology
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.InvolutionQuotient
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.M76.FreeInvolutionQuotient

variable {X : Type u} [TopologicalSpace X] (τ : X ≃ₜ X)
  (hτ : Function.Involutive τ)

def orbitSetoid : Setoid X where
  r x y := x = y ∨ x = τ y
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((congrArg τ h).trans (hτ y)).symm
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (hxy.trans (congrArg τ hyz))
      · exact Or.inl (hxy.trans ((congrArg τ hyz).trans (hτ z)))

abbrev Model := Quotient (orbitSetoid τ hτ)

def projection : X → Model τ hτ := Quotient.mk (orbitSetoid τ hτ)

theorem projection_eq (x y : X) :
    projection τ hτ x = projection τ hτ y ↔ x = y ∨ x = τ y := Quotient.eq

theorem projection_involution (x : X) : projection τ hτ (τ x) = projection τ hτ x :=
  Quotient.sound (Or.inr rfl)

theorem continuous_projection : Continuous (projection τ hτ) := continuous_quotient_mk'

theorem projection_isClosedMap : IsClosedMap (projection τ hτ) := by
  intro A hA
  apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
  have he : projection τ hτ ⁻¹' (projection τ hτ '' A) = A ∪ τ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      rcases (projection_eq τ hτ y x).mp he with he | he
      · exact Or.inl (he ▸ hy)
      · exact Or.inr (by change τ x ∈ A; exact he ▸ hy)
    · rintro (h | h)
      · exact ⟨x, h, rfl⟩
      · exact ⟨τ x, h, projection_involution τ hτ x⟩
  change IsClosed (projection τ hτ ⁻¹' (projection τ hτ '' A))
  rw [he]
  exact hA.union (hA.preimage τ.continuous)

instance [T2Space X] : T2Space (Model τ hτ) := by
  have hq := Poincare.Topology.isOpenQuotientMap_of_pair_fibers (orbitSetoid τ hτ) τ
    τ.continuous (fun _ _ => Iff.rfl)
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have he : {z : X × X | projection τ hτ z.1 = projection τ hτ z.2} =
      {z | z.1 = z.2} ∪ {z | z.1 = τ z.2} := by
    ext z
    exact projection_eq τ hτ z.1 z.2
  change IsClosed {z : X × X | projection τ hτ z.1 = projection τ hτ z.2}
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (τ.continuous.comp continuous_snd))

theorem projection_isCoveringMap [T2Space X] (hfree : ∀ x, τ x ≠ x) :
    IsCoveringMap (projection τ hτ) := by
  have hl := Poincare.Topology.Orientation.ProjectivePlane.involutionQuotient_isLocalHomeomorph
    (orbitSetoid τ hτ) τ hτ (fun x => (hfree x).symm) (fun _ _ => Iff.rfl)
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply (projection_isClosedMap τ hτ).isCoveringMapOn_of_isLocalHomeomorphOn
  · intro y _
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective y
    have he : projection τ hτ ⁻¹' {projection τ hτ a} = {a, τ a} := by
      ext x
      exact projection_eq τ hτ x a
    change (projection τ hτ ⁻¹' {projection τ hτ a}).Finite
    rw [he]
    exact (finite_singleton _).insert _
  · rw [preimage_univ]
    exact hl.isLocalHomeomorphOn

end PoincareConjecture.M76.FreeInvolutionQuotient
