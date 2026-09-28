import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure AlexanderHalfSlab (S : Set E) (A : E →ᵃ[ℝ] ℝ) (q : E) (β : ℝ) where

  width_pos : 0 < β

  apex_mem : q ∈ S

  apex_height : A q = 0

  upper : E → ℝ

  collar : Set E

  residual : Set E

  residualComplex : SimplicialComplex ℝ E

  chart : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (upper p.1)} ≃ₜ collar

  chart_finitePL : chart.IsFinitePL

  residual_finite : residualComplex.faces.Finite

  residual_space : residualComplex.space = residual

  cover : collar ∪ residual = S ∩ {x | A x ∈ Icc 0 β}

  residual_zero : residual ∩ {x | A x = 0} ⊆ {q}

  roof_contact : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (chart p : E) ∈ residual ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1

  radialTop : Set E

  contactTop : Set E

  residual_radial : ∀ c ∈ Ioo 0 β, residual ∩ {x | A x = c} =
    AffineMap.homothety q (c / β) '' radialTop

  contact_radial : ∀ c ∈ Ioo 0 β, (collar ∩ residual) ∩ {x | A x = c} =
    AffineMap.homothety q (c / β) '' contactTop

  upper_finitePL : FinitePiecewiseAffineOn upper (S ∩ {x | A x = 0})

  upper_bounds : ∀ x ∈ S ∩ {x | A x = 0}, upper x ∈ Icc 0 β

  apex_upper : upper q = 0

  upper_pos : ∀ x ∈ S ∩ {x | A x = 0}, x ≠ q → 0 < upper x

  height : ∀ p, A (chart p) = (p : E × ℝ).2

  bottom : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (upper p.1)},
    (p : E × ℝ).2 = 0 → (chart p : E) = (p : E × ℝ).1

  bottom_covered : S ∩ {x | A x = 0} ⊆ collar

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
