import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.RadialSimplex
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Simplices coned to the origin

Independent position vectors give an affinely independent simplex after
adjoining zero. Nonzero points of its cone hull lie on positive segments
to the base. See Cairns 1940, pp. 799, 801--802 and M76 derivation 19.
-/

set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adjoining zero to independent position vectors gives an affinely
independent set. See Cairns' conical stars on p. 799 and M76 derivation 19. -/
theorem LinearIndependent.affineIndependent_insert_zero {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    AffineIndependent ℝ ((↑) : ↥(insert (0 : E) s) → E) := by
  have hnonzero : ∀ x ∈ s, x ≠ (0 : E) := fun x hx he =>
    hs.zero_notMem_convexHull (he ▸ subset_convexHull ℝ s hx)
  have h := (linearIndependent_set_iff_affineIndependent_vadd_union_singleton
    ℝ hnonzero (0 : E)).mp hs
  let f : ↥(insert (0 : E) s) →
      ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' s) :=
    fun x => ⟨x.val, by
      rcases x.property with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨x.val, hx, by simp [vadd_eq_add]⟩⟩
  exact h.comp_embedding ⟨f, fun x y hxy => Subtype.ext
    (congrArg (fun z : ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' s) => (z : E)) hxy)⟩

/-- A nonzero point in the convex hull with zero adjoined lies on a
positive segment to a base-hull point. The base may initially be empty.
See Cairns pp. 799, 802 and M76 derivation 19. -/
theorem exists_pos_smul_of_mem_convexHull_insert_zero {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ (insert (0 : E) s)) (hx0 : x ≠ 0) :
    ∃ y ∈ convexHull ℝ s, ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  have hs : s.Nonempty := by
    by_contra hs
    exact hx0 (by simpa [Set.not_nonempty_iff_eq_empty.mp hs] using hx)
  rw [convexHull_insert hs, mem_convexJoin] at hx
  obtain ⟨p, hp, y, hy, a, b, ha, hb, hab, heq⟩ := hx
  rw [mem_singleton_iff] at hp
  subst p
  simp only [smul_zero, zero_add] at heq
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_smul] at heq
    exact hx0 heq.symm
  exact ⟨y, hy, b, ⟨lt_of_le_of_ne hb hb0.symm, by linarith⟩, heq.symm⟩

/-- The segment from zero to a base-hull point lies in the coned hull.
See Cairns pp. 799, 802 and M76 derivation 19. -/
theorem smul_mem_convexHull_insert_zero {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : r • x ∈ convexHull ℝ (insert (0 : E) s) :=
  (convex_convexHull ℝ _).smul_mem_of_zero_mem
    (subset_convexHull ℝ _ (Set.mem_insert _ _))
    (convexHull_mono (Set.subset_insert _ _) hx) hr
