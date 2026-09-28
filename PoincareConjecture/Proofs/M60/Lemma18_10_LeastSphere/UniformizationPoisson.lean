import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Poisson.Approximation
import PoincareConjecture.Proofs.M03.Existence.SpectralHeatNative











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}




theorem exists_weak_poisson_closed_surface (D : LeviCivitaData g)
    (F : Lp ℝ 2 (g.volumeMeasure.restrict univ))
    (hF : (∫ x, F x ∂g.volumeMeasure) = 0) :
    ∃ u : H1Zero D univ, ∀ v : H1Zero D univ,
      ⟪u, v⟫_ℝ - ⟪toDomainL2 D univ u, toDomainL2 D univ v⟫_ℝ =
        ⟪F, toDomainL2 D univ v⟫_ℝ := by
  let b := eigenbasis D univ (by norm_num) isOpen_univ (by simpa using isCompact_univ)
  obtain ⟨C, hC, hbound⟩ := exists_bound_inv_eigenvalue_compact D
  let S := SpectralHeatNative.multiplier (fun i => (eigenvalue D univ i)⁻¹) C hC hbound
  let U := b.repr.symm (S (b.repr F))
  have hU (i : EigenIndex D univ) :
      b.repr U i = (eigenvalue D univ i)⁻¹ * b.repr F i := by
    simp only [U, LinearIsometryEquiv.apply_symm_apply, S, SpectralHeatNative.multiplier_apply]
  let u := domainResolvent D univ (U + F)
  have hu : toDomainL2 D univ u = U := by
    change domainL2Resolvent D univ (U + F) = U
    apply b.repr.injective
    ext i
    change b.repr (domainL2Resolvent D univ (U + F)) i = b.repr U i
    rw [domainL2Resolvent_repr, map_add]
    change i.1.1 * (b.repr U i + b.repr F i) = b.repr U i
    rw [hU]
    by_cases hi : eigenvalue D univ i = 0
    · have hz := eigenbasis_repr_eq_zero_of_eigenvalue_eq_zero D F hF i hi
      change b.repr F i = 0 at hz
      simp only [hz, mul_zero, add_zero]
    · calc
        _ = i.1.1 * ((1 + eigenvalue D univ i) *
            ((eigenvalue D univ i)⁻¹ * b.repr F i)) := by
          rw [add_mul, one_mul, ← mul_assoc (eigenvalue D univ i),
            mul_inv_cancel₀ hi, one_mul]
        _ = _ := by rw [← mul_assoc, resolvent_eigenvalue_mul_one_add, one_mul]
  refine ⟨u, fun v => ?_⟩
  rw [hu]
  change ⟪domainResolvent D univ (U + F), v⟫_ℝ - _ = _
  rw [domainResolvent_inner, inner_add_left, add_sub_cancel_left]

end PoincareConjecture.M60
