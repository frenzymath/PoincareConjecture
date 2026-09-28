import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Extrema

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [CompactSpace M] {g : RiemannianMetric 2 M}

theorem scalar_eq_twice_scale_of_compact_round_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hround : ConstantPositiveSectionalCurvature g D) (x : M) :
    D.scalarCurvature x = 2 * lambda := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  obtain ⟨R, _, hR⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature D).mp hround
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn ⟨x, mem_univ x⟩ hfs.continuous.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hfs.continuous.continuousOn
  have hlo := D.scalar_le_twice_scale_of_potential_min hfs hsol
    (hp.isLocalMin (Filter.univ_mem))
  have hhi := D.twice_scale_le_scalar_of_potential_max hfs hsol
    (hq.isLocalMax (Filter.univ_mem))
  rw [hR p] at hlo
  rw [hR q] at hhi
  rw [hR x]
  exact le_antisymm hlo hhi

end PoincareConjecture.LeviCivitaData
