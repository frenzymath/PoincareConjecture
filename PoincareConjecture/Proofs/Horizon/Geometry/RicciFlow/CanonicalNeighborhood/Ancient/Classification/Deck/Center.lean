import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.DeckAction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Deck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder











noncomputable section
set_option autoImplicit false

open Set Function Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientCylinderDeck

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

variable {M : Type*} [TopologicalSpace M] (q : UnitTwoSphere × ℝ → M)


theorem exists_common_center
    (hsplit : ∀ d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ), q ∘ d = q →
      ∃ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (s c : ℝ),
        (s = 1 ∨ s = -1) ∧ ∀ z, d z = (sphereMotion L z.1, s * z.2 + c))
    (hperiod : ∀ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (c : ℝ), (∀ z, q (sphereMotion L z.1, z.2 + c) = q z) → c = 0) :
    ∃ a : ℝ, ∀ d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ), q ∘ d = q →
      ∃ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (s : ℝ),
        (s = 1 ∨ s = -1) ∧ ∀ z, d z = (sphereMotion L z.1, s * (z.2 - a) + a) := by
  classical
  by_cases href : ∃ (d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ))
      (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (c : ℝ),
      q ∘ d = q ∧ ∀ z, d z = (sphereMotion L z.1, -z.2 + c)
  · obtain ⟨d, L, c, hd, hform⟩ := href
    refine ⟨c / 2, fun e he => ?_⟩
    obtain ⟨A, s, b, hs, heform⟩ := hsplit e he
    refine ⟨A, s, hs, fun z => ?_⟩
    rcases hs with rfl | rfl
    · have hb : b = 0 := hperiod A b (fun w => by
        simpa only [comp_apply, heform, one_mul] using congrFun he w)
      rw [heform, hb]
      congr 1
      ring
    · have hb : c - b = 0 := hperiod (L * A) (c - b) (fun w => by
        have hh := (congrFun hd (e w)).trans (congrFun he w)
        simp only [comp_apply, heform, hform, neg_one_mul] at hh
        have hm : (sphereMotion (L * A) w.1, w.2 + (c - b)) =
            (sphereMotion L (sphereMotion A w.1), -(-w.2 + b) + c) :=
          Prod.ext (Subtype.ext rfl) (by ring)
        rw [hm]
        exact hh)
      rw [heform]
      congr 1
      linarith
  · refine ⟨0, fun d hd => ?_⟩
    obtain ⟨L, s, c, hs, hform⟩ := hsplit d hd
    rcases hs with rfl | rfl
    · have hc : c = 0 := hperiod L c (fun z => by
        simpa only [comp_apply, hform, one_mul] using congrFun hd z)
      exact ⟨L, 1, Or.inl rfl, fun z => by simpa [hc] using hform z⟩
    · exact (href ⟨d, L, c, hd, fun z => by simpa only [neg_one_mul] using hform z⟩).elim


theorem slice_orthogonal_group_free (hc : IsCoveringMap q) (a : ℝ)
    (L : RicciFlow.Splitting.orthogonalSurfaceDeckGroup (fun x => q (x, a)))
    (hL : L ≠ 1) (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) : L.val v ≠ v := by
  intro hfix
  let x : UnitTwoSphere := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
  have heq : (fun y : UnitTwoSphere => (sphereMotion L.val y, a)) =
      (fun y : UnitTwoSphere => (y, a)) :=
    hc.eq_of_comp_eq ((sphereMotion L.val).continuous.prodMk continuous_const)
      (continuous_id.prodMk continuous_const) (funext L.property) x
      (Prod.ext (Subtype.ext hfix) rfl)
  apply hL
  apply Subtype.ext
  apply RicciFlow.Splitting.surfaceMotion_injective
  funext y
  exact (congrArg Prod.fst (congrFun heq y)).trans (Subtype.ext rfl)


theorem sphereFactor_eq_antipodal (hc : IsCoveringMap q) (a : ℝ)
    (d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ)) (hd : q ∘ d = q)
    (hne : d ≠ Homeomorph.refl _)
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (s : ℝ)
    (hform : ∀ z, d z = (sphereMotion L z.1, s * (z.2 - a) + a)) :
    L = LinearIsometryEquiv.neg ℝ := by
  let H := RicciFlow.Splitting.orthogonalSurfaceDeckGroup (fun x => q (x, a))
  have hmem : L ∈ H := by
    intro x
    simpa only [comp_apply, hform, sub_self, mul_zero, zero_add] using congrFun hd (x, a)
  let l : H := ⟨L, hmem⟩
  have hl : l ≠ 1 := by
    intro h
    have hL : L = 1 := congrArg Subtype.val h
    let x : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp [UnitTwoSphere, UnitSphere]⟩
    apply hne
    apply Homeomorph.ext
    exact congrFun (hc.eq_of_comp_eq d.continuous continuous_id hd (x, a) (by
      change d (x, a) = (x, a)
      rw [hform, hL]
      exact Prod.ext (Subtype.ext rfl) (by ring)))
  exact RicciFlow.Splitting.free_orthogonalThree_subgroup_eq_antipodal H
    (slice_orthogonal_group_free q hc a) l hl

end PoincareConjecture.AncientCylinderDeck
