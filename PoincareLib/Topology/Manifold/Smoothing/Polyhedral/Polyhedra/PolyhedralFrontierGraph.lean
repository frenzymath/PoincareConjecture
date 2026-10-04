import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineMinimum
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.ContinuousGraphShear
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.OppositePolyhedralFrontierGerms
import Mathlib.Topology.Order.Lattice

/-!
# Actual polyhedral frontiers as finite affine graphs

At a pole whose radial coordinate is one, all active linear
halfspaces have radial coefficient one. Their frontier is
the graph of an attained finite affine minimum. Strict
inactive inequalities give the literal original frontier
germ. See Hudson 1969, pp. 12--19, Alexander 1924, pp. 6--8
and M76 derivation 286h.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

/-- The frontier of a continuous hypograph is exactly its
graph, by the ambient continuous graph shear. No regularity
beyond continuity is needed. See M76 derivation 286h. -/
theorem frontier_hypograph_eq_graph {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) :
    frontier {p : X × ℝ | p.2 ≤ f p.1} = {p | p.2 = f p.1} := by
  let h := Homeomorph.subContinuousGraph f hf
  have hpre : h ⁻¹' ((univ : Set X) ×ˢ Iic (0 : ℝ)) =
      {p : X × ℝ | p.2 ≤ f p.1} := by
    ext p
    change (True ∧ p.2 - f p.1 ≤ 0) ↔ p.2 ≤ f p.1
    simp only [true_and, sub_nonpos]
  rw [← hpre, ← h.preimage_frontier, frontier_univ_prod_eq, frontier_Iic]
  ext p
  change (True ∧ p.2 - f p.1 = 0) ↔ p.2 = f p.1
  simp only [true_and, sub_eq_zero]

end Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonempty finite family of linear halfspaces active
at the pole `(0,1)` has an exact global frontier graph.
The graph function is continuous, equals one at zero and
is finite PL on every finite geometric carrier. See
Hudson pp. 12--19 and M76 derivation 286h. -/
theorem exists_active_halfspace_frontier_graph
    (H : Finset ((E × ℝ) →ₗ[ℝ] ℝ)) (hH : H.Nonempty)
    (hactive : ∀ A ∈ H, A ((0 : E), (1 : ℝ)) = 1) :
    ∃ f : E → ℝ, Continuous f ∧ f 0 = 1 ∧
      (∀ x y, (∀ A ∈ H, A (x, y) ≤ 1) ↔ y ≤ f x) ∧
      frontier {p : E × ℝ | ∀ A ∈ H, A p ≤ 1} = {p | p.2 = f p.1} ∧
      ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn f K.space := by
  classical
  let f : E → ℝ := fun x => H.inf' hH (fun A => 1 - A (x, 0))
  have hf : Continuous f := Continuous.finset_inf'_apply hH fun A _ =>
    continuous_const.sub
      (A.continuous_of_finiteDimensional.comp (continuous_id.prodMk continuous_const))
  have hf0 : f 0 = 1 := by
    simp only [f, show ((0 : E), (0 : ℝ)) = (0 : E × ℝ) from rfl,
      map_zero, sub_zero, Finset.inf'_const]
  have hformula (A : (E × ℝ) →ₗ[ℝ] ℝ) (hAH : A ∈ H) (x : E) (y : ℝ) :
      A (x, y) = A (x, 0) + y := by
    have hsplit : (x, y) = (x, 0) + y • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hactive A hAH]
    simp only [smul_eq_mul, mul_one]
  have hbody (x : E) (y : ℝ) :
      (∀ A ∈ H, A (x, y) ≤ 1) ↔ y ≤ f x := by
    change (∀ A ∈ H, A (x, y) ≤ 1) ↔ y ≤ H.inf' hH (fun A => 1 - A (x, 0))
    rw [Finset.le_inf'_iff]
    constructor
    · intro h A hAH
      have hA := h A hAH
      rw [hformula A hAH x y] at hA
      linarith
    · intro h A hAH
      rw [hformula A hAH x y]
      linarith [h A hAH]
  have hset : {p : E × ℝ | ∀ A ∈ H, A p ≤ 1} = {p | p.2 ≤ f p.1} := by
    ext p
    exact hbody p.1 p.2
  refine ⟨f, hf, hf0, hbody, ?_, ?_⟩
  · rw [hset]
    exact frontier_hypograph_eq_graph f hf
  · intro K hK
    let : Nonempty {A // A ∈ H} := ⟨⟨hH.choose, hH.choose_spec⟩⟩
    let B : {A // A ∈ H} → E →ᵃ[ℝ] ℝ := fun A =>
      AffineMap.const ℝ E 1 - (A.val.comp (LinearMap.inl ℝ E ℝ)).toAffineMap
    apply K.finitePiecewiseAffineOn_of_affine_minimum hK B
    intro x _
    obtain ⟨A, hAH, hmin⟩ := Finset.exists_mem_eq_inf' hH (fun A => 1 - A (x, 0))
    refine ⟨⟨A, hAH⟩, ?_, ?_⟩
    · change f x = 1 - A (x, 0)
      exact hmin
    · intro j
      change H.inf' hH (fun A => 1 - A (x, 0)) ≤ 1 - j.val (x, 0)
      exact Finset.inf'_le _ j.property

/-- The complete original finite halfspace frontier near
the pole `(0,1)` is an actual finite affine graph. The open
germ lies in any prescribed open pole neighborhood; only
the inactive constraints are discarded locally. See
Hudson pp. 12--19 and M76 derivation 286h. -/
theorem exists_halfspace_frontier_graph_germ
    (H : Finset ((E × ℝ) →ₗ[ℝ] ℝ))
    (hp : ∀ A ∈ H, A ((0 : E), (1 : ℝ)) ≤ 1)
    (hactive : ∃ A ∈ H, A ((0 : E), (1 : ℝ)) = 1)
    {U : Set (E × ℝ)} (hU : IsOpen U) (hpU : ((0 : E), (1 : ℝ)) ∈ U) :
    ∃ (f : E → ℝ) (V : Set (E × ℝ)),
      Continuous f ∧ f 0 = 1 ∧ IsOpen V ∧ ((0 : E), (1 : ℝ)) ∈ V ∧ V ⊆ U ∧
      {p : E × ℝ | ∀ A ∈ H, A p ≤ 1} ∩ V = {p | p.2 ≤ f p.1} ∩ V ∧
      frontier {p : E × ℝ | ∀ A ∈ H, A p ≤ 1} ∩ V =
        {p | p.2 = f p.1} ∩ V ∧
      ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn f K.space := by
  classical
  let G := H.filter fun A => A ((0 : E), (1 : ℝ)) = 1
  let I := H.filter fun A => A ((0 : E), (1 : ℝ)) ≠ 1
  have hG : G.Nonempty := by
    obtain ⟨A, hAH, hAp⟩ := hactive
    exact ⟨A, Finset.mem_filter.mpr ⟨hAH, hAp⟩⟩
  obtain ⟨f, hf, hf0, hbody, hfront, hfPL⟩ :=
    exists_active_halfspace_frontier_graph G hG
      (fun A hA => (Finset.mem_filter.mp hA).2)
  let V := U ∩ {x : E × ℝ | ∀ A ∈ I, A x < 1}
  have hstrict : IsOpen {x : E × ℝ | ∀ A ∈ I, A x < 1} := by
    simp only [ofPred_forall]
    exact isOpen_biInter_finset fun A _ =>
      isOpen_lt A.continuous_of_finiteDimensional continuous_const
  have hV : IsOpen V := hU.inter hstrict
  have hpV : ((0 : E), (1 : ℝ)) ∈ V := by
    refine ⟨hpU, ?_⟩
    intro A hA
    have h := Finset.mem_filter.mp hA
    exact lt_of_le_of_ne (hp A h.1) h.2
  have heq : {p : E × ℝ | ∀ A ∈ H, A p ≤ 1} ∩ V =
      {p : E × ℝ | ∀ A ∈ G, A p ≤ 1} ∩ V := by
    apply Subset.antisymm
    · exact fun x hx => ⟨fun A hA => hx.1 A (Finset.mem_filter.mp hA).1, hx.2⟩
    · rintro x ⟨hx, hxV⟩
      refine ⟨?_, hxV⟩
      intro A hAH
      by_cases hAp : A ((0 : E), (1 : ℝ)) = 1
      · exact hx A (Finset.mem_filter.mpr ⟨hAH, hAp⟩)
      · exact (hxV.2 A (Finset.mem_filter.mpr ⟨hAH, hAp⟩)).le
  refine ⟨f, V, hf, hf0, hV, hpV, inter_subset_left, ?_, ?_, hfPL⟩
  · rw [heq]
    congr 1
    ext p
    exact hbody p.1 p.2
  · rw [frontier_inter_eq_of_inter_eq_open hV heq, hfront]

end Geometry.SimplicialComplex
