import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace Poincare.Geometry.RicciFlow.Harnack

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_comp_manifold_spacetimePath
    {f : ℝ × M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) f (t, γ t))
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t) :
    HasDerivAt (fun s ↦ f (s, γ s))
      (deriv (fun s ↦ f (s, γ t)) t +
        mvfderiv (𝓡 n) (fun x ↦ f (t, x)) (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) t := by
  have hpath := (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk hγ.hasMFDerivAt
  have h := (hf.hasMFDerivAt.comp t hpath).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun s ↦ f (s, γ s))
    (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) f (t, γ t)
      (1, mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) t at h
  rw [mfderiv_prod_eq_add_apply hf] at h
  simpa only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, mvfderiv,
    ContinuousLinearMap.comp_apply] using! h

theorem scalarCurvature_hasDerivAt_path
    {J : Set ℝ} (hM04 : PoincareConjecture.RicciFlowCurvatureTheory.{u})
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ}
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ (F.connection s).scalarCurvature (γ s))
      (deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
        mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) t := by
  have hJnhds : J ∈ nhds t := Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hJ
  apply hasDerivAt_comp_manifold_spacetimePath
    (f := fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (γ := γ)
  · exact ((hM04.scalar_regular n M J F).mdifferentiableOn (by simp)
      (t, γ t) ⟨hJ (Ioo_subset_Icc_self ht), mem_univ _⟩).mdifferentiableAt
      (prod_mem_nhds hJnhds Filter.univ_mem)
  · exact (hγ.mdifferentiableOn (by simp) t (Ioo_subset_Icc_self ht)).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)

end Poincare.Geometry.RicciFlow.Harnack
