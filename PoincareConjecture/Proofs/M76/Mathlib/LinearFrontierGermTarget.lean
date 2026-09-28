import PoincareConjecture.Proofs.M76.Mathlib.OppositePolyhedralFrontierGerms












set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem linear_halfspace_bounds_and_active_of_mem_frontier
    (H : Finset (E →ₗ[ℝ] ℝ)) {p : E}
    (hp : p ∈ frontier {x : E | ∀ A ∈ H, A x ≤ 1}) :
    (∀ A ∈ H, A p ≤ 1) ∧ ∃ A ∈ H, A p = 1 := by
  have hclosed : IsClosed {x : E | ∀ A ∈ H, A x ≤ 1} := by
    simp only [ofPred_forall]
    exact isClosed_biInter fun A _ =>
      isClosed_le A.continuous_of_finiteDimensional continuous_const
  have hbound : ∀ A ∈ H, A p ≤ 1 := hclosed.frontier_subset hp
  refine ⟨hbound, ?_⟩
  by_contra hactive
  have hstrict : ∀ A ∈ H, A p < 1 := by
    intro A hAH
    exact lt_of_le_of_ne (hbound A hAH) (fun heq => hactive ⟨A, hAH, heq⟩)
  have hopen : IsOpen {x : E | ∀ A ∈ H, A x < 1} := by
    simp only [ofPred_forall]
    exact isOpen_biInter_finset fun A _ =>
      isOpen_lt A.continuous_of_finiteDimensional continuous_const
  exact hp.2 (interior_maximal
    (fun x (hx : ∀ A ∈ H, A x < 1) A hA => (hx A hA).le) hopen hstrict)

end Set

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem exists_convex_target_of_negatively_collinear_frontier_germs
    {C : Set E} (H : Finset (E →ₗ[ℝ] ℝ))
    (hC : C = {x | ∀ A ∈ H, A x ≤ 1})
    (ea eb : E ≃L[ℝ] F) {a b : E} {p q : F} {r : ℝ}
    (hr : 0 < r) (hpq : q = -(r • p))
    (ha : a ∈ frontier C) (hb : b ∈ frontier C)
    (hea : ea a = p) (heb : eb b = q) :
    ∃ (K : SimplicialComplex ℝ F) (U V : Set F),
      K.faces.Finite ∧ IsCompact K.space ∧ Convex ℝ K.space ∧
      (0 : F) ∈ interior K.space ∧ IsOpen U ∧ p ∈ U ∧
      IsOpen V ∧ q ∈ V ∧ Disjoint U V ∧
      K.space ∩ U = (ea '' C) ∩ U ∧
      K.space ∩ V = (eb '' C) ∩ V ∧
      frontier K.space ∩ U = (ea '' frontier C) ∩ U ∧
      frontier K.space ∩ V = (eb '' frontier C) ∩ V ∧
      p ∈ frontier K.space ∧ q ∈ frontier K.space := by
  classical
  have himage (e : E ≃L[ℝ] F) :
      e '' C = {y | ∀ A ∈ H.image (fun L => L.comp e.symm.toLinearMap), A y ≤ 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ A hA
      obtain ⟨L, hLH, rfl⟩ := Finset.mem_image.mp hA
      change L (e.symm (e x)) ≤ 1
      rw [e.symm_apply_apply]
      exact (hC ▸ hx) L hLH
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [hC]
      intro L hLH
      exact hy (L.comp e.symm.toLinearMap) (Finset.mem_image.mpr ⟨L, hLH, rfl⟩)
  let HA := H.image fun L => L.comp ea.symm.toLinearMap
  let HB := H.image fun L => L.comp eb.symm.toLinearMap
  have hpA : p ∈ frontier {y | ∀ A ∈ HA, A y ≤ 1} := by
    rw [← himage ea]
    change p ∈ frontier (ea.toHomeomorph '' C)
    rw [← ea.toHomeomorph.image_frontier]
    exact ⟨a, ha, hea⟩
  have hpB : q ∈ frontier {y | ∀ A ∈ HB, A y ≤ 1} := by
    rw [← himage eb]
    change q ∈ frontier (eb.toHomeomorph '' C)
    rw [← eb.toHomeomorph.image_frontier]
    exact ⟨b, hb, heb⟩
  have hA := linear_halfspace_bounds_and_active_of_mem_frontier HA hpA
  have hB := linear_halfspace_bounds_and_active_of_mem_frontier HB hpB
  obtain ⟨K, U, V, hK, hcompact, hconvex, hzero, hU, hpU, hV, hpV,
    hdis, hbodyU, hbodyV, hfrontU, hfrontV, hpK, hnK⟩ :=
    exists_convex_body_negatively_collinear_halfspace_germs HA HB p q hr hpq
      hA.1 hB.1 hA.2 hB.2
  have hbodyU' : K.space ∩ U = (ea '' C) ∩ U := by
    rw [himage ea]
    exact hbodyU
  have hbodyV' : K.space ∩ V = (eb '' C) ∩ V := by
    rw [himage eb]
    exact hbodyV
  have hfrontU' : frontier K.space ∩ U = (ea '' frontier C) ∩ U := by
    have heq : (ea '' frontier C) = frontier {y | ∀ A ∈ HA, A y ≤ 1} := by
      change (ea.toHomeomorph '' frontier C) = _
      rw [ea.toHomeomorph.image_frontier]
      change frontier (ea '' C) = _
      rw [himage ea]
    rw [heq]
    exact hfrontU
  have hfrontV' : frontier K.space ∩ V = (eb '' frontier C) ∩ V := by
    have heq : (eb '' frontier C) = frontier {y | ∀ A ∈ HB, A y ≤ 1} := by
      change (eb.toHomeomorph '' frontier C) = _
      rw [eb.toHomeomorph.image_frontier]
      change frontier (eb '' C) = _
      rw [himage eb]
    rw [heq]
    exact hfrontV
  exact ⟨K, U, V, hK, hcompact, hconvex, hzero, hU, hpU, hV, hpV,
    hdis, hbodyU', hbodyV', hfrontU', hfrontV', hpK, hnK⟩







theorem exists_convex_target_of_linear_frontier_germs
    {C : Set E} (H : Finset (E →ₗ[ℝ] ℝ))
    (hC : C = {x | ∀ A ∈ H, A x ≤ 1})
    (ea eb : E ≃L[ℝ] F) {a b : E} {p : F}
    (ha : a ∈ frontier C) (hb : b ∈ frontier C)
    (hea : ea a = p) (heb : eb b = -p) :
    ∃ (K : SimplicialComplex ℝ F) (U V : Set F),
      K.faces.Finite ∧ IsCompact K.space ∧ Convex ℝ K.space ∧
      (0 : F) ∈ interior K.space ∧ IsOpen U ∧ p ∈ U ∧
      IsOpen V ∧ -p ∈ V ∧ Disjoint U V ∧
      K.space ∩ U = (ea '' C) ∩ U ∧
      K.space ∩ V = (eb '' C) ∩ V ∧
      frontier K.space ∩ U = (ea '' frontier C) ∩ U ∧
      frontier K.space ∩ V = (eb '' frontier C) ∩ V ∧
      p ∈ frontier K.space ∧ -p ∈ frontier K.space := by
  exact exists_convex_target_of_negatively_collinear_frontier_germs H hC ea eb
    zero_lt_one (by rw [one_smul]) ha hb hea heb

end Geometry.SimplicialComplex
