import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapBoundaryChart
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]

structure HamiltonMarkedCapCoordinates {D S : Set X} {eps : ℝ}
    (g : S × Ico (0 : ℝ) eps → X) where
  original : OpenPartialHomeomorph X (ℝ × E)
  boundary : OpenPartialHomeomorph S E
  chart : OpenPartialHomeomorph X (ℝ × E)
  radius : ℝ
  lateral : Set E
  radius_pos : 0 < radius
  radius_le : radius ≤ eps
  lateral_open : IsOpen lateral
  rectangle : Set.prod (Ioo (-radius) radius) lateral ⊆ original.target
  boundary_source : boundary.source = Subtype.val ⁻¹' original.source
  boundary_target : boundary.target = {z | (0, z) ∈ original.target}
  boundary_forward : ∀ x : S, boundary x = (original x).2
  boundary_inverse : ∀ z ∈ boundary.target,
    (boundary.symm z : X) = original.symm (0, z)
  original_side : ∀ x ∈ original.source, x ∈ D ↔ (original x).1 ≤ 0
  target : chart.target = Set.prod (Ioo (-radius) radius) lateral
  source : chart.source = original.symm '' Set.prod (Ico (0 : ℝ) radius) lateral ∪
    {x | ∃ z ∈ lateral, ∃ t : Ico (0 : ℝ) eps, (t : ℝ) < radius ∧
      g (boundary.symm z, t) = x}
  positive : ∀ p : Set.prod (Ico (0 : ℝ) radius) lateral,
    chart (original.symm (p : ℝ × E)) = (p : ℝ × E)
  negative : ∀ z ∈ lateral, ∀ t : Ico (0 : ℝ) eps, (t : ℝ) < radius →
    chart (g (boundary.symm z, t)) = (-(t : ℝ), z)

namespace HamiltonMarkedCapCoordinates

variable {D S : Set X} {eps : ℝ} {g : S × Ico (0 : ℝ) eps → X}
  (c : HamiltonMarkedCapCoordinates (E := E) (D := D) g)

theorem inverse_nonneg (p : ℝ × E) (hp : p ∈ c.chart.target) (ht : 0 ≤ p.1) :
    c.chart.symm p = c.original.symm p := by
  have hp' := c.target.subset hp
  have hpP : p ∈ Set.prod (Ico (0 : ℝ) c.radius) c.lateral := ⟨⟨ht, hp'.1.2⟩, hp'.2⟩
  have hx : c.original.symm p ∈ c.chart.source := by
    rw [c.source]
    exact Or.inl (mem_image_of_mem _ hpP)
  have h := congrArg c.chart.symm (c.positive ⟨p, hpP⟩)
  rw [c.chart.left_inv hx] at h
  exact h.symm

theorem inverse_nonpos (p : ℝ × E) (hp : p ∈ c.chart.target) (ht : p.1 ≤ 0) :
    ∃ t : Ico (0 : ℝ) eps, (t : ℝ) = -p.1 ∧ (t : ℝ) < c.radius ∧
      c.chart.symm p = g (c.boundary.symm p.2, t) := by
  have hp' := c.target.subset hp
  let t : Ico (0 : ℝ) eps := ⟨-p.1, neg_nonneg.mpr ht, by
    linarith [hp'.1.1, c.radius_le]⟩
  have htr : (t : ℝ) < c.radius := by dsimp [t]; linarith [hp'.1.1]
  have hx : g (c.boundary.symm p.2, t) ∈ c.chart.source := by
    rw [c.source]
    exact Or.inr ⟨p.2, hp'.2, t, htr, rfl⟩
  have h := congrArg c.chart.symm (c.negative p.2 hp'.2 t htr)
  rw [c.chart.left_inv hx] at h
  have hpval : (-(t : ℝ), p.2) = p := by dsimp [t]; exact Prod.ext (neg_neg p.1) rfl
  rw [hpval] at h
  exact ⟨t, rfl, htr, h.symm⟩

theorem side (hg : ∀ p, g p ∈ D) (x : X) (hx : x ∈ c.chart.source) :
    x ∈ D ↔ (c.chart x).1 ≤ 0 := by
  let p := c.chart x
  have hp : p ∈ c.chart.target := c.chart.map_source hx
  by_cases ht : 0 ≤ p.1
  · have hpinv := c.inverse_nonneg p hp ht
    have hpB : p ∈ c.original.target := c.rectangle (c.target.subset hp)
    have hxB : x ∈ c.original.source := by
      rw [← c.chart.left_inv hx, hpinv]
      exact c.original.map_target hpB
    have hval : c.original x = p := by
      rw [← c.chart.left_inv hx, hpinv, c.original.right_inv hpB]
    exact (c.original_side x hxB).trans (by rw [hval])
  · have ht' : p.1 ≤ 0 := (lt_of_not_ge ht).le
    obtain ⟨t, _, _, hval⟩ := c.inverse_nonpos p hp ht'
    have hxD : x ∈ D := by
      rw [← c.chart.left_inv hx, hval]
      exact hg _
    exact ⟨fun _ => ht', fun _ => hxD⟩

theorem interior_side (hg : ∀ p, g p ∈ D) (x : X) (hx : x ∈ c.chart.source) :
    x ∈ interior D ↔ (c.chart x).1 < 0 := by
  have hi : c.chart.IsImage D {p | p.1 ≤ 0} := fun {y} hy => (c.side hg y hy).symm
  have heq : interior {p : ℝ × E | p.1 ≤ 0} = {p | p.1 < 0} := by
    change interior ((Prod.fst : ℝ × E → ℝ) ⁻¹' Iic 0) =
      (Prod.fst : ℝ × E → ℝ) ⁻¹' Iio 0
    rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Iic]
  have h := hi.interior.apply_mem_iff hx
  rw [heq] at h
  exact h.symm

theorem coordinates_nonneg (p : ℝ × E) (hp : p ∈ c.chart.target) (ht : 0 ≤ p.1) :
    c.chart.symm p ∈ c.original.source ∧ c.original (c.chart.symm p) = p := by
  have hpB : p ∈ c.original.target := c.rectangle (c.target.subset hp)
  rw [c.inverse_nonneg p hp ht]
  exact ⟨c.original.map_target hpB, c.original.right_inv hpB⟩

theorem lateral_subset_boundary_target : c.lateral ⊆ c.boundary.target := by
  intro z hz
  rw [c.boundary_target]
  exact c.rectangle ⟨⟨neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩, hz⟩

end HamiltonMarkedCapCoordinates

end PoincareConjecture.M76
