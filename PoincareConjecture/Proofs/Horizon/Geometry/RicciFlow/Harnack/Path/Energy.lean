import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace Poincare.Geometry.RicciFlow.Harnack

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

theorem continuousOn_spacetimeEnergyWithin_integrand
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b)) :
    ContinuousOn (fun t ↦ (F.metric t).inner (γ t)
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ (Icc a b) t 1)
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ (Icc a b) t 1)) (Icc a b) := by
  have htangent := hγ.contMDiffOn_tangentMapWithin (m := 0) (by simp)
    (uniqueDiffOn_Icc hab).uniqueMDiffOn
  have hunit : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) 0
      (fun t : ℝ ↦ (⟨t, 1⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) (Icc a b) := by
    intro t ht
    simp only [Bundle.contMDiffWithinAt_totalSpace,
      trivializationAt_model_space_apply]
    exact ⟨contMDiffWithinAt_id, contMDiffWithinAt_const⟩
  have hv := htangent.comp hunit (fun t ht ↦ ht)
  have hg := (F.smooth.of_le (show (0 : WithTop ℕ∞) ≤ ∞ from by simp)).comp
    (contMDiffOn_id.prodMk (hγ.of_le (by simp)))
    (fun t ht ↦ ⟨hJ ht, mem_univ (γ t)⟩)
  have heval := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hv hv
  intro t ht
  have hpoint := heval t ht
  simp only [Bundle.contMDiffWithinAt_totalSpace] at hpoint
  exact hpoint.2.continuousWithinAt

theorem spacetimeEnergyWithin_integrand_eqOn
    (F : PoincareConjecture.RicciFlow n M J) (γ : ℝ → M) (a b : ℝ) :
    EqOn (fun t ↦ (F.metric t).inner (γ t)
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ (Icc a b) t 1)
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ (Icc a b) t 1))
      (fun t ↦ (F.metric t).inner (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) (Ioo a b) := by
  intro t ht
  dsimp only
  rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
    (Icc_mem_nhds ht.1 ht.2)]

theorem intervalIntegrable_spacetimeEnergy_integrand
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b)) :
    IntervalIntegrable (fun t ↦ (F.metric t).inner (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) volume a b := by
  have hc := continuousOn_spacetimeEnergyWithin_integrand F hab hJ γ hγ
  apply (hc.intervalIntegrable_of_Icc hab.le).congr_uIoo
  rw [uIoo_of_le hab.le]
  exact spacetimeEnergyWithin_integrand_eqOn F γ a b

theorem continuousOn_spacetimeEnergy_integrand
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b)) :
    ContinuousOn (fun t ↦ (F.metric t).inner (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) (Ioo a b) := by
  have hc := continuousOn_spacetimeEnergyWithin_integrand F hab hJ γ hγ
  exact (hc.mono Ioo_subset_Icc_self).congr
    (spacetimeEnergyWithin_integrand_eqOn F γ a b).symm

end Poincare.Geometry.RicciFlow.Harnack
