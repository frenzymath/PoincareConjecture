import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryTrace














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







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

end PoincareConjecture.M64Uniformization
