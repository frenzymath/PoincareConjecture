import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.AlexanderRecursiveSlab

/-!
# The collar geometry actually consumed by recursive surgery

The protected isotopy needs a complete finite PL collar and
its exact residual roof contact, but no radial formula for
that residual. The stronger original half-slab projects to
this core witness. See Alexander 1924, pp. 7--8 and
M76 derivation 256.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual geometric collar and finite residual used by
the recursive protected isotopy. It records exact coverage
and roof contact but does not prescribe a radial form for
the residual. See Alexander pp. 7--8 and derivation 256. -/
structure AlexanderCollarSlab (S : Set E) (A : E →ᵃ[ℝ] ℝ) (q : E) (β : ℝ) where
  /-- The closed slab has positive width. -/
  width_pos : 0 < β
  /-- The marked point belongs to the actual surface. -/
  apex_mem : q ∈ S
  /-- The marked point is at the bottom height. -/
  apex_height : A q = 0
  /-- The variable collar roof on the complete bottom section. -/
  upper : E → ℝ
  /-- The actual collar image. -/
  collar : Set E
  /-- The actual complementary residual in the slab. -/
  residual : Set E
  /-- A finite triangulation of the residual. -/
  residualComplex : SimplicialComplex ℝ E
  /-- The actual height-preserving collar chart. -/
  chart : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (upper p.1)} ≃ₜ collar
  /-- The chart is finite PL on its exact source. -/
  chart_finitePL : chart.IsFinitePL
  /-- The residual triangulation is finite. -/
  residual_finite : residualComplex.faces.Finite
  /-- The residual triangulation has exactly the specified carrier. -/
  residual_space : residualComplex.space = residual
  /-- Collar and residual cover the exact original closed slab. -/
  cover : collar ∪ residual = S ∩ {x | A x ∈ Icc 0 β}
  /-- Only the marked point can lie in the residual bottom. -/
  residual_zero : residual ∩ {x | A x = 0} ⊆ {q}
  /-- The residual meets each collar fiber exactly at its roof. -/
  roof_contact : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (chart p : E) ∈ residual ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1
  /-- The roof is finite PL on the complete bottom section. -/
  upper_finitePL : FinitePiecewiseAffineOn upper (S ∩ {x | A x = 0})
  /-- Every roof value lies in the actual slab height range. -/
  upper_bounds : ∀ x ∈ S ∩ {x | A x = 0}, upper x ∈ Icc 0 β
  /-- The marked fiber collapses. -/
  apex_upper : upper q = 0
  /-- Every other bottom point has a positive collar fiber. -/
  upper_pos : ∀ x ∈ S ∩ {x | A x = 0}, x ≠ q → 0 < upper x
  /-- The actual affine height is the collar fiber coordinate. -/
  height : ∀ p, A (chart p) = (p : E × ℝ).2
  /-- The collar fixes its bottom pointwise. -/
  bottom : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (p : E × ℝ).2 = 0 → (chart p : E) = (p : E × ℝ).1
  /-- Every original bottom point belongs to the collar. -/
  bottom_covered : S ∩ {x | A x = 0} ⊆ collar

/-- An original radial half-slab supplies the core collar
witness without adding any conclusion or hypothesis.
See Alexander pp. 7--8 and M76 derivation 256. -/
def AlexanderHalfSlab.toCollarSlab {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderHalfSlab S A q β) :
    AlexanderCollarSlab S A q β where
  width_pos := M.width_pos
  apex_mem := M.apex_mem
  apex_height := M.apex_height
  upper := M.upper
  collar := M.collar
  residual := M.residual
  residualComplex := M.residualComplex
  chart := M.chart
  chart_finitePL := M.chart_finitePL
  residual_finite := M.residual_finite
  residual_space := M.residual_space
  cover := M.cover
  residual_zero := M.residual_zero
  roof_contact := M.roof_contact
  upper_finitePL := M.upper_finitePL
  upper_bounds := M.upper_bounds
  apex_upper := M.apex_upper
  upper_pos := M.upper_pos
  height := M.height
  bottom := M.bottom
  bottom_covered := M.bottom_covered

/-- The marked collar fiber consists of the actual marked
point because its roof is zero. See Alexander p. 8 and
M76 derivation 256. -/
theorem AlexanderCollarSlab.chart_eq_apex_of_base_eq {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    (p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) (hp : (p : E × ℝ).1 = q) :
    (M.chart p : E) = q := by
  have hz : (p : E × ℝ).2 = 0 := by
    apply le_antisymm _ p.property.2.1
    simpa only [hp, M.apex_upper] using p.property.2.2
  exact (M.bottom p hz).trans hp

/-- The residual contains the marked point, which is the
upper endpoint of its collapsed collar fiber. See Alexander
p. 8 and M76 derivation 256. -/
theorem AlexanderCollarSlab.apex_mem_residual {S : Set E} {A : E →ᵃ[ℝ] ℝ}
    {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β) : q ∈ M.residual := by
  let p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} :=
    ⟨(q, 0), ⟨M.apex_mem, M.apex_height⟩, le_rfl, M.apex_upper.symm.le⟩
  have hp : (M.chart p : E) = q := M.chart_eq_apex_of_base_eq p rfl
  have hmem : (M.chart p : E) ∈ M.residual :=
    (M.roof_contact p).mpr M.apex_upper.symm
  rw [hp] at hmem
  exact hmem

end Geometry
