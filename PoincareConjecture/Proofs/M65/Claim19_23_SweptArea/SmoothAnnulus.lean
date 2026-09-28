import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.CompactLipschitz
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.AnnulusDomain

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def m65AnnulusOfContMDiff (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    {c0 c1 : ℝ → M}
    (hperiodic : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x, f (annulusPoint x 1) = c1 x) : M64Annulus g c0 c1 := by
  let bound := m65Exists_compact_lipschitz_constant g hf
    m65AnnulusDomain_isCompact m65AnnulusDomain_convex
  exact {
    map := f
    continuous_on_domain := hf.continuous.continuousOn
    periodic := hperiodic
    lower_boundary := hlower
    upper_boundary := hupper
    lipschitz_constant := Classical.choose bound
    lipschitz_nonnegative := (Classical.choose_spec bound).1
    lipschitz_on_domain := (Classical.choose_spec bound).2
    ae_manifold_differentiable := Filter.Eventually.of_forall
      (fun _ _ => hf.mdifferentiableAt one_ne_zero)
    area_integrable := (m65Continuous_areaDensity g hf).continuousOn.integrableOn_compact
      m65AnnulusDomain_isCompact
  }

@[simp] theorem m65AnnulusOfContMDiff_map (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) {c0 c1 : ℝ → M}
    (hp : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (h0 : ∀ x, f (annulusPoint x 0) = c0 x) (h1 : ∀ x, f (annulusPoint x 1) = c1 x) :
    (m65AnnulusOfContMDiff g f hf hp h0 h1).map = f := rfl

end PoincareConjecture
