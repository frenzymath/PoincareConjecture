import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.Twisted








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Topology

noncomputable section

universe u

namespace PoincareConjecture.AncientCylinderQuotient

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  (q : UnitTwoSphere × ℝ → M) (hq : Function.Surjective q)
  (hd : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)

include hq hd

omit [IsManifold (𝓡 3) ∞ M] in
theorem exists_projectivePlaneCoordinates
    (hfib : ∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, p.2)) :
    ∃ e : M ≃ₜ (RealProjectiveTwo × ℝ),
      ∀ p, e (q p) = (Quotient.mk' p.1, p.2) := by
  let proj : UnitTwoSphere × ℝ → RealProjectiveTwo × ℝ :=
    Prod.map Quotient.mk' id
  have hp : IsOpenQuotientMap proj :=
    (isOpenQuotientMap_of_pair_fibers _ Neg.neg continuous_neg
      (fun _ _ => Iff.rfl)).prodMap IsOpenQuotientMap.id
  let f : C(UnitTwoSphere × ℝ, M) := ⟨q, hd.contMDiff.continuous⟩
  let g : C(UnitTwoSphere × ℝ, RealProjectiveTwo × ℝ) := ⟨proj, hp.continuous⟩
  have hf : Topology.IsQuotientMap f :=
    (show IsOpenQuotientMap q from ⟨hq, hd.contMDiff.continuous, hd.isOpenMap⟩).isQuotientMap
  have hfg : ∀ p p', f p = f p' ↔ g p = g p' := by
    intro p p'
    change q p = q p' ↔
      (Quotient.mk' p.1, p.2) = (Quotient.mk' p'.1, p'.2)
    rw [hfib]
    constructor
    · rintro (rfl | rfl)
      · rfl
      · apply Prod.ext
        · exact Quotient.sound (Or.inr (by simp))
        · rfl
    · intro h
      have hs := Quotient.exact (congrArg Prod.fst h)
      have hl := congrArg Prod.snd h
      rcases hs with hs | hs
      · exact Or.inl (Prod.ext hs.symm hl.symm)
      · exact Or.inr (Prod.ext (by rw [hs]; simp) hl.symm)
  refine ⟨hf.homeomorphOfFibers hp.isQuotientMap hfg, ?_⟩
  exact hf.homeomorphOfFibers_apply hp.isQuotientMap hfg

omit [IsManifold (𝓡 3) ∞ M] in
theorem exists_twistedProjectiveCoordinates
    (hfib : ∀ p p', q p = q p' ↔ p' = p ∨ p' = m27TwistedProductInvolution p) :
    ∃ e : M ≃ₜ PuncturedRealProjectiveThree twistedProjectivePuncture,
      ∀ p, e (q p) = twistedProjectiveMap p := by
  let f : C(UnitTwoSphere × ℝ, M) := ⟨q, hd.contMDiff.continuous⟩
  let g : C(UnitTwoSphere × ℝ,
      PuncturedRealProjectiveThree twistedProjectivePuncture) :=
    ⟨twistedProjectiveMap, twistedProjectiveMap_isOpenQuotientMap.continuous⟩
  have hf : Topology.IsQuotientMap f :=
    (show IsOpenQuotientMap q from ⟨hq, hd.contMDiff.continuous, hd.isOpenMap⟩).isQuotientMap
  have hg : Topology.IsQuotientMap g := twistedProjectiveMap_isOpenQuotientMap.isQuotientMap
  have hfg : ∀ p p', f p = f p' ↔ g p = g p' := by
    intro p p'
    change q p = q p' ↔ twistedProjectiveMap p = twistedProjectiveMap p'
    rw [hfib, twistedProjectiveMap_fibers]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (by simp [m27TwistedProductInvolution])
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp [m27TwistedProductInvolution])
  exact ⟨hf.homeomorphOfFibers hg hfg, hf.homeomorphOfFibers_apply hg hfg⟩

theorem exists_twistedProjectiveSmoothModel
    (hfib : ∀ p p', q p = q p' ↔ p' = p ∨ p' = m27TwistedProductInvolution p) :
    ∃ e : M ≃ₜ PuncturedRealProjectiveThree twistedProjectivePuncture,
      ∃ C : StandardPuncturedProjectiveCover M twistedProjectivePuncture Set.univ,
        ∀ (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ twistedProjectivePuncture),
          e (C.cover x) = ⟨Quotient.mk' x, hx⟩ := by
  obtain ⟨e, he⟩ := exists_twistedProjectiveCoordinates q hq hd hfib
  let cover : UnitThreeSphere → M := fun x => q (spherePolarInverseTotal 2 x)
  have hcoord (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ twistedProjectivePuncture) :
      e (cover x) = ⟨Quotient.mk' x, hx⟩ := by
    have hx' := (spherePolarDomain_projective x).mpr hx
    change e (q (spherePolarInverseTotal 2 x)) = _
    rw [he]
    apply Subtype.ext
    change Quotient.mk realProjectiveThreeSetoid
      (spherePolarMap (spherePolarInverseTotal 2 x)) = Quotient.mk' x
    have h := spherePolar_right_inv (⟨x, hx'⟩ : spherePolarDomain 2)
    rw [spherePolarInverseTotal_coe ⟨x, hx'⟩, h]
    rfl
  refine ⟨e, ⟨cover, ?_, ?_, ?_⟩, hcoord⟩
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := Quotient.mk'_surjective (e y).val
    have hp : Quotient.mk' x ≠ twistedProjectivePuncture := by
      rw [hx]
      exact (e y).property
    refine ⟨x, hp, e.injective ?_⟩
    rw [hcoord x hp]
    exact Subtype.ext hx
  · intro x y hx hy
    constructor
    · intro h
      have heq := congrArg e h
      rw [hcoord x hx, hcoord y hy] at heq
      exact Quotient.exact (congrArg Subtype.val heq)
    · intro h
      apply e.injective
      rw [hcoord x hx, hcoord y hy]
      exact Subtype.ext (Quotient.sound h)
  · intro x
    have hx := (spherePolarDomain_projective x.val).mpr x.property
    have hp := (spherePolarPartialDiffeomorph 2).symm.isLocalDiffeomorphAt
      (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ hx
    exact hp.comp (𝓡 3) M (hd _)

end PoincareConjecture.AncientCylinderQuotient
