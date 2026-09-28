import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Poisson.Spectrum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

omit [PreconnectedSpace M] in
theorem exists_smooth_eigenbasis_representative (D : LeviCivitaData g)
    (i : EigenIndex D univ) :
    ∃ U : M → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ U ∧
      U =ᵐ[g.volumeMeasure] (eigenbasis D univ (by norm_num) isOpen_univ
        (by simpa using isCompact_univ) i : M → ℝ) ∧
      ∀ x, -D.laplacian U x = eigenvalue D univ i * U x := by
  obtain ⟨U, hU, hUae, hEq⟩ := exists_smooth_eigenfunction_representative D
    (by norm_num) isOpen_univ
    (energyEigenfunction D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i) (eigenvalue D univ i)
    (energyEigenfunction_equation D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i)
  refine ⟨U, contMDiffOn_univ.mp hU, ?_, fun x => hEq x (mem_univ x)⟩
  have hdom := toDomainL2_ae
    (energyEigenfunction D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i)
  rw [toDomainL2_energyEigenfunction] at hdom
  have hdom' : (eigenbasis D univ (by norm_num) isOpen_univ
      (by simpa using isCompact_univ) i : M → ℝ) =ᵐ[g.volumeMeasure]
      (toL2 D univ (energyEigenfunction D univ (by norm_num) isOpen_univ
        (by simpa using isCompact_univ) i) : M → ℝ) := by
    simpa only [Measure.restrict_univ] using hdom
  have hUae' : U =ᵐ[g.volumeMeasure]
      (toL2 D univ (energyEigenfunction D univ (by norm_num) isOpen_univ
        (by simpa using isCompact_univ) i) : M → ℝ) := by
    simpa only [Measure.restrict_univ] using hUae
  filter_upwards [hUae', hdom'] with x hx hy
  exact hx.trans hy.symm

end PoincareConjecture.LeviCivitaData.Dirichlet
