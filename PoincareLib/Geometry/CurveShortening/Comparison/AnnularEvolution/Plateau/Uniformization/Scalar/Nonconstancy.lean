import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.BoundaryTrace

/-!
# Nonconstancy forced by the actual annular boundary traces

The fixed smooth boundary extension takes values 0 and 1 on the two
boundary circles. If its sum with a zero-boundary H1 correction were
constant, the correction would have the smooth representative `c - q`.
Its proved zero trace at the two circles gives a contradiction. No boundary
continuity of the unknown harmonic representative is assumed.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- Every potential with the prescribed annular H1 boundary data is nonconstant,
independently of whether it minimizes energy. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarPotential_not_ae_constant (w : H1Zero D scalarAnnulus) (c : ℝ) :
    ¬ (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
      annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)
        =ᵐ[g.volumeMeasure.restrict scalarAnnulus] (fun _ => c) := by
  intro hconst
  let q := annularBoundaryExtension
  let hq := annularBoundaryExtension_smooth
  let hqc := annularBoundaryExtension_compact
  have hwq : (toL2 D scalarAnnulus w : Plane → ℝ)
      =ᵐ[g.volumeMeasure.restrict scalarAnnulus] (fun x => c - q x) := by
    filter_upwards [hconst, ae_restrict_of_ae (Lp.coeFn_add
      ((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q)
      (toL2 D scalarAnnulus w)),
      ae_restrict_of_ae ((hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp)]
      with x hx hxadd hxq
    change ((((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q) +
      toL2 D scalarAnnulus w : Lp ℝ 2 g.volumeMeasure) : Plane → ℝ) x = c at hx
    rw [hxadd, Pi.add_apply, hxq] at hx
    linarith
  let a0 : Plane := EuclideanSpace.single (0 : Fin 2) 1
  let a1 : Plane := EuclideanSpace.single (0 : Fin 2) 2
  have ha0 : ‖a0‖ = 1 := by simp [a0]
  have ha1 : ‖a1‖ = 2 := by norm_num [a1]
  have h0 := H1Zero_smooth_annular_trace_zero D w (contMDiff_const.sub hq) hwq
    (Or.inl ha0)
  have h1 := H1Zero_smooth_annular_trace_zero D w (contMDiff_const.sub hq) hwq
    (Or.inr ha1)
  change c - annularBoundaryExtension a0 = 0 at h0
  change c - annularBoundaryExtension a1 = 0 at h1
  rw [annularBoundaryExtension_inner ha0] at h0
  rw [annularBoundaryExtension_outer ha1] at h1
  linarith

/-- The actual constructed smooth interior harmonic potential is nonconstant because it
retains the two different H1 boundary traces. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_annular_nonconstant_smooth_harmonic_potential :
    ∃ (H : Plane → ℝ) (w : H1Zero D scalarAnnulus),
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (¬ ∃ c : ℝ, EqOn H (fun _ => c) scalarAnnulus) ∧
      ∀ v : H1Zero D scalarAnnulus,
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w ≤
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact v := by
  obtain ⟨H, w, hHs, hHae, hHlap, hmin⟩ := exists_annular_smooth_harmonic_potential D
  refine ⟨H, w, hHs, hHae, hHlap, ?_, hmin⟩
  rintro ⟨c, hc⟩
  apply scalarPotential_not_ae_constant D w c
  apply hHae.symm.trans
  filter_upwards [ae_restrict_mem scalarAnnulus_isOpen.measurableSet] with x hx
  exact hc hx

end PoincareMT.M64Uniformization
