import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarStrictRange
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.RepresentativeDerivative
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarPotential_partial_memLp (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (i : Fin 2) :
    MemLp (fun x => fderiv ℝ H x (EuclideanSpace.single i 1)) 2
      (volume.restrict scalarAnnulus) := by
  let q := annularBoundaryExtension
  let hq := annularBoundaryExtension_smooth
  let hqc := annularBoundaryExtension_compact
  let U : Plane → ℝ := fun x => H x - q x
  have hUs : ContDiffOn ℝ ∞ U scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).sub (contMDiff_iff_contDiff.mp hq).contDiffOn
  have hUae : U =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (toL2 D scalarAnnulus w : Plane → ℝ) := by
    filter_upwards [hHae, ae_restrict_of_ae (Lp.coeFn_add
      ((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q)
      (toL2 D scalarAnnulus w)),
      ae_restrict_of_ae ((hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp)]
      with x hx hxadd hxq
    change H x = ((((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q) +
      toL2 D scalarAnnulus w : Lp ℝ 2 g.volumeMeasure) : Plane → ℝ) x at hx
    rw [hxadd, Pi.add_apply, hxq] at hx
    change H x - q x = _
    linarith
  have hOK : scalarAnnulus ⊆ {x : Plane | 0 ≤ scalarAnnulusDefining x} :=
    fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le
  let P : Lp ℝ 2 (volume.restrict scalarAnnulus) :=
    localCoordinateDerivative (OpenPartialHomeomorph.refl Plane)
      contMDiffOn_id contMDiffOn_id scalarClosedAnnulus_isCompact (by simp) hOK
      (EuclideanSpace.single i 1) w
  have hP : (P : Plane → ℝ) =ᵐ[volume.restrict scalarAnnulus]
      fun x => fderiv ℝ U x (EuclideanSpace.single i 1) :=
    HarmonicCoordinates.localCoordinateDerivative_id_eq_fderiv_ae
      scalarClosedAnnulus_isCompact hOK scalarAnnulus_isOpen subset_rfl w hUs hUae i
  have hUp : MemLp (fun x => fderiv ℝ U x (EuclideanSpace.single i 1)) 2
      (volume.restrict scalarAnnulus) := MemLp.ae_eq hP (Lp.memLp P)
  have hqs := contMDiff_iff_contDiff.mp hq
  have hqp : MemLp (fun x => fderiv ℝ q x (EuclideanSpace.single i 1)) 2
      (volume.restrict scalarAnnulus) :=
    (((hqs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hqc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict scalarAnnulus
  apply MemLp.ae_eq ?_ (hUp.add hqp)
  filter_upwards [ae_restrict_mem scalarAnnulus_isOpen.measurableSet] with x hx
  have hdx := (contMDiffAt_iff_contDiffAt.mp
    (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds hx))).differentiableAt (by simp)
  have hd : fderiv ℝ U x = fderiv ℝ H x - fderiv ℝ q x :=
    fderiv_sub hdx (hqs.differentiable (by simp) x)
  change fderiv ℝ U x (EuclideanSpace.single i 1) +
    fderiv ℝ q x (EuclideanSpace.single i 1) = _
  rw [hd]
  simp

theorem scalarPotential_finite_differential_energy (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)) :
    IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus := by
  have hi (i : Fin 2) : IntegrableOn
      (fun x => (fderiv ℝ H x (EuclideanSpace.single i 1)) ^ 2) scalarAnnulus :=
    (scalarPotential_partial_memLp D w hHs hHae i).integrable_sq
  have heq (x : Plane) : ‖fderiv ℝ H x‖ ^ 2 =
      ∑ i : Fin 2, (fderiv ℝ H x (EuclideanSpace.single i 1)) ^ 2 := by
    simpa only [EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).norm_dual (fderiv ℝ H x)
  simp_rw [heq]
  exact integrable_finsetSum _ (fun i _ => hi i)

theorem exists_finite_energy_annular_harmonic_potential :
    ∃ (H : Plane → ℝ) (u : H1Zero D scalarAnnulus),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact u : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      (∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) ∧
      IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus ∧
      ∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v := by
  obtain ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter, hrange, hforce⟩ :=
    exists_strict_annular_harmonic_potential D
  exact ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter, hrange,
    scalarPotential_finite_differential_energy D u hHs hHae, hforce⟩

end PoincareConjecture.M64Uniformization
