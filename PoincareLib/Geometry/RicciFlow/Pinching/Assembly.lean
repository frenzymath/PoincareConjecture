import PoincareLib.Geometry.RicciFlow.Pinching.Bounds
import PoincareLib.Geometry.RicciFlow.Pinching.Persistence
import PoincareLib.Geometry.RicciFlow.Pinching.Definitions
import PoincareLib.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareLib.Geometry.RicciFlow.Pinching.GeometricPreservation.TimeEvolution

/-!
# Full-norm consumer for persistent Hamilton--Ivey pinching

The geometric spectrum is constructed from M04 curvature calculus. Logarithmic
pinching persistence then gives the project constant `13 * max R₀ (exp 4)`
for the original curvature norm and absolute time variable.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem full_norm_bound_of_persistent_hamiltonIvey
    [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : ∀ x : M,
      -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (hlog : ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-((F.connection t).leastSectionalCurvature x)) 0 →
        2 * max (-((F.connection t).leastSectionalCurvature x)) 0 *
            (Real.log (max (-((F.connection t).leastSectionalCurvature x)) 0) +
              Real.log (1 + t) - 3) ≤
          (F.connection t).scalarCurvature x) :
    ((∀ t ∈ Set.Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x) ∧
    (∀ R₀ : ℝ, ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ R₀ →
      (F.connection t).curvatureTensorNorm x ≤
        13 * max R₀ (Real.exp 4))) := by
  constructor
  · exact scalar_lower_bound_persists_of_M04 ha hab F hM04 hinit
  · intro R₀ t ht x hR
    obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
      (F.connection t).three_dimensional_curvature_spectrum
        (hM04.tensor_calculus 3 M (F.metric t) (F.connection t)) x
    have hpinch : 0 < max (-k3) 0 →
        2 * max (-k3) 0 * (Real.log (max (-k3) 0) + Real.log (1 + t) - 3) ≤
          2 * (k1 + k2 + k3) := by
      intro hX
      simpa [hleast, hscalar] using hlog t ht x (by simpa [hleast] using hX)
    rw [hscalar] at hR
    exact Poincare.fullNorm_le_of_hamiltonIvey (k1 := k1) (k2 := k2) (k3 := k3)
      (N := (F.connection t).curvatureTensorNorm x) (R := 2 * (k1 + k2 + k3))
      (R₀ := R₀) (t := t) (ha.trans ht.1) h12 h23 rfl hnorm hR hpinch

/-! This packages the scalar logarithmic producer with the already checked
three-spectrum and full-norm consumers.  The compact maximum-principle route
only has to provide `hlog`; no spectral witness is supplied as an assumption. -/

theorem pinching_persistence_and_bounds_of_log
    [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : ∀ x : M,
      -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (hlog : ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-((F.connection t).leastSectionalCurvature x)) 0 →
        2 * max (-((F.connection t).leastSectionalCurvature x)) 0 *
            (Real.log (max (-((F.connection t).leastSectionalCurvature x)) 0) +
              Real.log (1 + t) - 3) ≤
          (F.connection t).scalarCurvature x) :
    (∀ t ∈ Set.Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x) ∧
    (∀ t ∈ Set.Ico a b, ∀ x : M, ∃ k1 k2 k3 : ℝ,
      k1 ≥ k2 ∧ k2 ≥ k3 ∧
      (F.connection t).leastSectionalCurvature x = k3 ∧
      (F.connection t).scalarCurvature x = 2 * (k1 + k2 + k3) ∧
      (F.connection t).curvatureTensorNorm x ^ 2 =
        4 * (k1 ^ 2 + k2 ^ 2 + k3 ^ 2)) ∧
    (∀ R₀ : ℝ, ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ R₀ →
      (F.connection t).curvatureTensorNorm x ≤
        13 * max R₀ (Real.exp 4)) := by
  have hbounds := full_norm_bound_of_persistent_hamiltonIvey ha hab F hM04 hinit hlog
  refine ⟨hbounds.1, ?_, hbounds.2⟩
  intro t ht x
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    (F.connection t).three_dimensional_curvature_spectrum
      (hM04.tensor_calculus 3 M (F.metric t) (F.connection t)) x
  exact ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩

/-! A conditional consequence for spectra satisfying the reaction ODE. Actual
Ricci-flow curvature evolves by a PDE with a spatial Laplacian, so the displayed
ODE hypotheses are not the missing geometric maximum-principle theorem. That
theorem must establish the logarithmic estimate used by the consumer above. -/

theorem full_norm_bound_of_ordered_reaction
    [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : ∀ x : M,
      -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (lam mu nu : M → ℝ → ℝ)
    (hlam : ∀ x : M, ContinuousOn (lam x) (Set.Icc a b))
    (hmu : ∀ x : M, ContinuousOn (mu x) (Set.Icc a b))
    (hnu : ∀ x : M, ContinuousOn (nu x) (Set.Icc a b))
    (hord : ∀ x : M, ∀ t ∈ Set.Icc a b,
      mu x t ≤ lam x t ∧ nu x t ≤ mu x t)
    (hdlam : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (lam x) (lam x t ^ 2 + mu x t * nu x t) t)
    (hdmu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (mu x) (mu x t ^ 2 + lam x t * nu x t) t)
    (hdnu : ∀ x : M, ∀ t ∈ Set.Ioo a b,
      HasDerivAt (nu x) (nu x t ^ 2 + lam x t * mu x t) t)
    (hleast : ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).leastSectionalCurvature x = nu x t)
    (hscalar : ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x = 2 * (lam x t + mu x t + nu x t))
    (hlogInit : ∀ x : M,
      0 < max (-((F.connection a).leastSectionalCurvature x)) 0 →
        2 * max (-((F.connection a).leastSectionalCurvature x)) 0 *
            (Real.log (max (-((F.connection a).leastSectionalCurvature x)) 0) +
              Real.log (1 + a) - 3) ≤
          (F.connection a).scalarCurvature x) :
    ((∀ t ∈ Set.Ico a b, ∀ x : M,
      -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x) ∧
    (∀ R₀ : ℝ, ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ R₀ →
      (F.connection t).curvatureTensorNorm x ≤
        13 * max R₀ (Real.exp 4))) := by
  have ha_mem : a ∈ Set.Ico a b := ⟨le_rfl, hab⟩
  have htrace : ∀ x : M,
      -6 / (1 + 4 * a) ≤ 2 * (lam x a + mu x a + nu x a) := by
    intro x
    rw [← hscalar a ha_mem x]
    exact hinit x
  have hlog : ∀ t ∈ Set.Ico a b, ∀ x : M,
      0 < max (-((F.connection t).leastSectionalCurvature x)) 0 →
        2 * max (-((F.connection t).leastSectionalCurvature x)) 0 *
            (Real.log (max (-((F.connection t).leastSectionalCurvature x)) 0) +
              Real.log (1 + t) - 3) ≤
          (F.connection t).scalarCurvature x := by
    have hlog' := geometric_log_pinching_of_initial_data ha hab lam mu nu
      hlam hmu hnu hord hdlam hdmu hdnu htrace (by
        intro x hX
        have hX' : 0 < max (-((F.connection a).leastSectionalCurvature x)) 0 := by
          simpa [hleast a ha_mem x] using hX
        have hh := hlogInit x hX'
        simpa [hleast a ha_mem x, hscalar a ha_mem x] using hh)
    intro t ht x hX
    rw [hleast t ht x, hscalar t ht x]
    exact hlog' t ht x (by simpa [hleast t ht x] using hX)
  exact full_norm_bound_of_persistent_hamiltonIvey ha hab F hM04 hinit hlog

end PoincareMT
