import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Poisson.Harmonic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.InteriorRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Compactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem eigenbasis_ae_const_of_eigenvalue_eq_zero (D : LeviCivitaData g)
    (i : EigenIndex D univ) (hi : eigenvalue D univ i = 0) :
    ∃ c : ℝ, (eigenbasis D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i : M → ℝ) =ᵐ[g.volumeMeasure.restrict univ]
        fun _ => c := by
  obtain ⟨U, hUs, hUae, hUeq⟩ := exists_smooth_eigenfunction_representative D
    (by norm_num) isOpen_univ
    (energyEigenfunction D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i) (eigenvalue D univ i)
    (energyEigenfunction_equation D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i)
  obtain ⟨c, hc⟩ := D.exists_eq_const_of_laplacian_eq_zero_compact
    (contMDiffOn_univ.mp hUs) (fun x => by simpa [hi] using hUeq x (mem_univ x))
  refine ⟨c, ?_⟩
  have hdom := toDomainL2_ae
    (energyEigenfunction D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i)
  rw [toDomainL2_energyEigenfunction] at hdom
  filter_upwards [hdom, hUae] with x hx hy
  exact hx.trans (hy.symm.trans (hc x))

theorem eigenbasis_repr_eq_zero_of_eigenvalue_eq_zero (D : LeviCivitaData g)
    (F : Lp ℝ 2 (g.volumeMeasure.restrict univ))
    (hF : (∫ x, F x ∂g.volumeMeasure) = 0)
    (i : EigenIndex D univ) (hi : eigenvalue D univ i = 0) :
    (eigenbasis D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ)).repr F i = 0 := by
  obtain ⟨c, hc⟩ := eigenbasis_ae_const_of_eigenvalue_eq_zero D i hi
  rw [HilbertBasis.repr_apply_apply, L2.inner_def]
  have heq : (∫ x, ⟪eigenbasis D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i x, F x⟫_ℝ ∂g.volumeMeasure.restrict univ) =
      ∫ x, c * F x ∂g.volumeMeasure := by
    rw [setIntegral_univ]
    apply integral_congr_ae
    have hc' : (eigenbasis D univ (by norm_num) isOpen_univ
        (by simpa using isCompact_univ) i : M → ℝ) =ᵐ[g.volumeMeasure] fun _ => c := by
      simpa only [Measure.restrict_univ] using hc
    filter_upwards [hc'] with x hx
    simp [hx, mul_comm]
  rw [heq, integral_const_mul, hF, mul_zero]

omit [PreconnectedSpace M] in

theorem exists_bound_inv_eigenvalue_compact (D : LeviCivitaData g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : EigenIndex D univ, |(eigenvalue D univ i)⁻¹| ≤ C := by
  have hfinite := finite_eigenvalue_le D univ (by norm_num) isOpen_univ
    (by simpa using isCompact_univ) 1
  obtain ⟨C, hC⟩ := (hfinite.image (fun i => |(eigenvalue D univ i)⁻¹|)).bddAbove
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun i => ?_⟩
  by_cases hi : eigenvalue D univ i ≤ 1
  · exact (hC (mem_image_of_mem _ hi)).trans (le_max_left _ _)
  · have hp : 1 ≤ eigenvalue D univ i := (lt_of_not_ge hi).le
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hp))]
    exact (inv_le_one_of_one_le₀ hp).trans (le_max_right _ _)

end PoincareConjecture.LeviCivitaData.Dirichlet
