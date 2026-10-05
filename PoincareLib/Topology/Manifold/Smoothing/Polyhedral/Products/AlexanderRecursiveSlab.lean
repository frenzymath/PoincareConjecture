import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLSubsets

/-!
# Actual Alexander half-slabs independent of image triangulations

The geometric witness retains a finite PL variable-roof collar,
its finite residual and both exact radial contact formulas.
Equality on the closed slab preserves the same geometry. See
Alexander 1924, pp. 6--8, Hudson pp. 12--19 and derivation 256.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit positive half-slab geometry used by Alexander
surgery. This records the actual collar and residual data,
without a genericity condition on a global triangulation.
It is not a recursive sphere or ball conclusion. See Alexander
pp. 6--8 and M76 derivation 256. -/
structure AlexanderHalfSlab (S : Set E) (A : E →ᵃ[ℝ] ℝ) (q : E) (β : ℝ) where
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
  /-- The retained top section for residual radial images. -/
  radialTop : Set E
  /-- The retained top section for collar contacts. -/
  contactTop : Set E
  /-- Every intermediate residual section is the actual radial image. -/
  residual_radial : ∀ c ∈ Ioo 0 β, residual ∩ {x | A x = c} =
    AffineMap.homothety q (c / β) '' radialTop
  /-- Every intermediate collar contact is the actual radial image. -/
  contact_radial : ∀ c ∈ Ioo 0 β, (collar ∩ residual) ∩ {x | A x = c} =
    AffineMap.homothety q (c / β) '' contactTop
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

/-- Equality on the actual closed slab transports its complete
half-slab witness. The same roof, image sets, finite residual
and radial top sections are used. See Alexander pp. 7--8
and derivation 256. -/
theorem AlexanderHalfSlab.nonempty_of_slab_eq {S S' : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderHalfSlab S A q β)
    (hslab : S ∩ {x | A x ∈ Icc 0 β} = S' ∩ {x | A x ∈ Icc 0 β}) :
    Nonempty (AlexanderHalfSlab S' A q β) := by
  have hbase : S ∩ {x | A x = 0} = S' ∩ {x | A x = 0} := by
    have hzero (x : E) (hx : A x = 0) : A x ∈ Icc 0 β := by
      rw [hx]
      exact ⟨le_rfl, M.width_pos.le⟩
    ext x
    exact ⟨fun hx => ⟨(hslab.subset ⟨hx.1, hzero x hx.2⟩).1, hx.2⟩,
      fun hx => ⟨(hslab.symm.subset ⟨hx.1, hzero x hx.2⟩).1, hx.2⟩⟩
  have hdomain : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} =
      {p : E × ℝ | p.1 ∈ S' ∩ {x | A x = 0} ∧ p.2 ∈ Icc 0 (M.upper p.1)} := by
    rw [hbase]
  let C := (Homeomorph.setCongr hdomain.symm).trans
    (M.chart.trans (Homeomorph.setCongr rfl))
  refine ⟨{
    width_pos := M.width_pos
    apex_mem := (hbase.subset ⟨M.apex_mem, M.apex_height⟩).1
    apex_height := M.apex_height
    upper := M.upper
    collar := M.collar
    residual := M.residual
    residualComplex := M.residualComplex
    chart := C
    chart_finitePL := M.chart_finitePL.setCongr hdomain rfl
    residual_finite := M.residual_finite
    residual_space := M.residual_space
    cover := M.cover.trans hslab
    residual_zero := M.residual_zero
    roof_contact := fun p => M.roof_contact ⟨p, hdomain.symm ▸ p.property⟩
    radialTop := M.radialTop
    contactTop := M.contactTop
    residual_radial := M.residual_radial
    contact_radial := M.contact_radial
    upper_finitePL := hbase ▸ M.upper_finitePL
    upper_bounds := fun x hx => M.upper_bounds x (hbase.symm ▸ hx)
    apex_upper := M.apex_upper
    upper_pos := fun x hx => M.upper_pos x (hbase.symm ▸ hx)
    height := fun p => M.height ⟨p, hdomain.symm ▸ p.property⟩
    bottom := fun p => M.bottom ⟨p, hdomain.symm ▸ p.property⟩
    bottom_covered := hbase.symm.subset.trans M.bottom_covered }⟩

end Geometry
