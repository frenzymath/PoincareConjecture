import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.OppositePolyhedralFrontierGerms

/-!
# A common target for two actual linear frontier germs

Transport the complete original halfspace body by the two
prescribed linear equivalences. Frontier membership supplies
the active constraints, and the opposite-pole construction
retains both actual linear body and frontier images locally.
See Hudson 1969, pp. 12--19, Alexander 1924, pp. 6--8 and
M76 derivation 286g.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A point on the frontier of a finite linear halfspace
region satisfies all original bounds and at least one exact
active equality. Strict satisfaction of all finitely many
bounds would give an open neighborhood inside the body.
See Hudson pp. 12--19 and M76 derivation 286g. -/
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

/-- Two unchanged linear maps of the original finite halfspace
frontier fit one compact convex target when their actual poles
lie at arbitrary positive distances on opposite rays. Both
literal body and frontier image germs are retained. See
Alexander pp. 6--8 and M76 derivation 286l. -/
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

/-- Two prescribed linear maps of the same actual finite
halfspace frontier, carrying their marked points to opposite
poles, fit one constructed compact convex target. Exact body
and frontier image germs are retained on disjoint open target
neighborhoods, without altering either prescribed map.
See Alexander pp. 6--8 and M76 derivation 286g. -/
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
