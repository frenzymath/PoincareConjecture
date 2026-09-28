import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Deck.Center
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Product

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientCylinderDeck

theorem fiber_alternatives {M : Type*} [TopologicalSpace M]
    (q : UnitTwoSphere × ℝ → M) (hc : IsCoveringMap q)
    (hsplit : ∀ d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ), q ∘ d = q →
      ∃ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (s c : ℝ),
        (s = 1 ∨ s = -1) ∧ ∀ z, d z = (sphereMotion L z.1, s * z.2 + c))
    (hperiod : ∀ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (c : ℝ), (∀ z, q (sphereMotion L z.1, z.2 + c) = q z) → c = 0) :
    Injective q ∨
      (∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, p.2)) ∨
      ∃ a : ℝ, ∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, 2 * a - p.2) := by
  classical
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : SimplyConnectedSpace (UnitTwoSphere × ℝ) :=
    Poincare.Topology.simplyConnectedSpace_prod_contractible
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  by_cases hinj : Injective q
  · exact Or.inl hinj
  obtain ⟨p₀, p₁, heq, hne⟩ := not_injective_iff.mp hinj
  obtain ⟨d, hd, hdp⟩ := Poincare.Topology.exists_covering_transformation hc p₀ p₁ heq
  have hdne : d ≠ Homeomorph.refl _ := by
    intro h
    have hh : d p₀ = p₀ := by rw [h]; rfl
    exact hne (hh.symm.trans hdp)
  obtain ⟨a, hcenter⟩ := exists_common_center q hsplit hperiod
  obtain ⟨L, s, hs, hform⟩ := hcenter d hd
  have hL := sphereFactor_eq_antipodal q hc a d hd hdne L s hform
  have htwo (e : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ)) (he : q ∘ e = q) :
      e = Homeomorph.refl _ ∨ e = d := by
    by_cases hene : e = Homeomorph.refl _
    · exact Or.inl hene
    right
    obtain ⟨A, r, _, heform⟩ := hcenter e he
    have hA := sphereFactor_eq_antipodal q hc a e he hene A r heform
    apply Homeomorph.ext
    exact congrFun (hc.eq_of_comp_eq e.continuous d.continuous (he.trans hd.symm)
      (p₀.1, a) (by simp only [heform, hform, hA, hL, sub_self, mul_zero, zero_add]))
  have hfib (p p' : UnitTwoSphere × ℝ) :
      q p = q p' ↔ p' = p ∨ p' = d p := by
    constructor
    · intro h
      obtain ⟨e, he, hep⟩ := Poincare.Topology.exists_covering_transformation hc p p' h
      rcases htwo e he with rfl | rfl
      · exact Or.inl hep.symm
      · exact Or.inr hep.symm
    · rintro (rfl | rfl)
      · rfl
      · exact (congrFun hd p).symm
  right
  have hneg (x : UnitTwoSphere) : sphereMotion (LinearIsometryEquiv.neg ℝ) x = -x :=
    Subtype.ext rfl
  rcases hs with rfl | rfl
  · left
    intro p p'
    simpa only [hform, hL, hneg, one_mul, sub_add_cancel] using hfib p p'
  · right
    refine ⟨a, fun p p' => ?_⟩
    have hh : d p = (-p.1, 2 * a - p.2) := by
      rw [hform, hL, hneg]
      exact Prod.ext rfl (by ring)
    simpa only [hh] using hfib p p'

end PoincareConjecture.AncientCylinderDeck
