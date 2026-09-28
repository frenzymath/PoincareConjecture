import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.Factorization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.FactorMetrics
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.Rigidity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.SphereFactor







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}



theorem involution_eq_antipodal_identity_or_reflection (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    (∀ p : q.product.surface × ℝ,
      q.involution p = (q.product.surface_sphere.symm (-(q.product.surface_sphere p.1)), p.2)) ∨
      ∃ c : ℝ, ∀ p : q.product.surface × ℝ,
        q.involution p =
          (q.product.surface_sphere.symm (-(q.product.surface_sphere p.1)), 2 * c - p.2) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.surface_charted
  let := q.product.surface_manifold
  obtain ⟨f, g, hf, hg, hfi, hgi, hfactor⟩ := q.exists_smooth_factorization
  let a := q.product.surface_sphere
  let F : UnitTwoSphere → UnitTwoSphere := fun x ↦ a (f (a.symm x))
  have hF : Isometry F := q.factor_sphere_isometry f g hf hfi hfactor
  have hFi : Function.Involutive F := by
    intro x
    simp only [F, a.symm_apply_apply]
    rw [hfi (a.symm x), a.apply_symm_apply]
  have hfree : ∀ x z, (F x, g z) ≠ (x, z) := by
    intro x z heq
    apply q.involution_free (a.symm x, z)
    rw [hfactor]
    apply Prod.ext
    · apply a.injective
      exact (congrArg Prod.fst heq).trans (a.apply_symm_apply x).symm
    · exact congrArg (fun p : UnitTwoSphere × ℝ ↦ p.2) heq
  let s₀ : q.product.surface :=
    a.symm ⟨EuclideanSpace.single 0 1, by simp⟩
  have hgd : Differentiable ℝ g := hg.contDiff.differentiable (by simp)
  have hG : Isometry g := real_isometry_of_involutive_deriv_sq hgd hgi
    (q.factor_line_deriv_sq f g hfactor s₀)
  rcases Poincare.Geometry.free_product_involutive_isometry_normal_forms
      hF hG hFi hgi hfree with hid | ⟨c, href⟩
  · left
    rintro ⟨s, z⟩
    rw [hfactor]
    have h := hid (a s) z
    apply Prod.ext
    · apply a.injective
      change a (f s) = a (a.symm (-a s))
      rw [a.apply_symm_apply]
      simpa only [F, a.symm_apply_apply] using congrArg Prod.fst h
    · exact congrArg (fun p : UnitTwoSphere × ℝ ↦ p.2) h
  · right
    refine ⟨c, ?_⟩
    rintro ⟨s, z⟩
    rw [hfactor]
    have h := href (a s) z
    apply Prod.ext
    · apply a.injective
      change a (f s) = a (a.symm (-a s))
      rw [a.apply_symm_apply]
      simpa only [F, a.symm_apply_apply] using congrArg Prod.fst h
    · exact congrArg (fun p : UnitTwoSphere × ℝ ↦ p.2) h

end PoincareConjecture.QuotientSphereLineCertificate
