import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction






set_option autoImplicit false
open Set
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology



theorem PoincareConjecture.LeviCivitaData.regularLevel_sectionalError_bounds
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (m + 2) M}
    (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (t : ℝ) {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x, f x = t → 0 ≤ K x)
    (hsec : ∀ x, f x = t → ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -K x ≤ D.sectionalCurvature x v w)
    {β : ℝ} (hβ : 0 ≤ β)
    (hhess : ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v) :
    let U := g.regularDomain hf
    let hreg := g.regularDomain_regular hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) t
    letI := isManifold_openLevelSet hf U hreg (m + 1) t
    let gL := PoincareConjecture.RiemannianMetric.regularLevelMetric hf U hreg t g
    let E := D.levelSectionalError f K β ∘ openLevelIncl f U t
    Continuous E ∧ ∀ z : openLevelSet f U t, 0 ≤ E z ∧
      ∀ v w : TangentSpace (𝓡 (m + 1)) z,
        -E z ≤ gL.leviCivitaData.sectionalCurvature z v w := by
  let U := g.regularDomain hf
  let hreg := g.regularDomain_regular hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg (m + 1) t
  let := isManifold_openLevelSet hf U hreg (m + 1) t
  let gL := PoincareConjecture.RiemannianMetric.regularLevelMetric hf U hreg t g
  let incl := openLevelIncl f U t
  let E := D.levelSectionalError f K β ∘ incl
  refine ⟨(D.continuousOn_levelSectionalError_regularDomain hf hKc β).comp_continuous
    (contMDiff_openLevelIncl hf U hreg (m + 1) t).continuous (fun z => z.1.2), ?_⟩
  intro z
  have hEn : 0 ≤ E z := D.levelSectionalError_nonneg f K hβ (hK (incl z) z.2)
  refine ⟨hEn, ?_⟩
  apply gL.leviCivitaData.sectionalCurvature_lower_bound_of_orthonormal z (neg_nonpos.mpr hEn)
  intro u v hu hv huv
  have htan (w : TangentSpace (𝓡 (m + 1)) z) :
      g.inner (incl z) (D.gradient f (incl z))
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) incl z w) = 0 := by
    have hk : mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f (incl z)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) incl z w) = 0 := by
      change mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) incl z w ∈
        (mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f (incl z)).ker
      rw [← range_mfderiv_openLevelIncl hf U hreg (m + 1) t z]
      exact ⟨w, rfl⟩
    rw [D.inner_gradient]
    have hk' := congrArg (fun q => NormedSpace.fromTangentSpace (f (incl z)) q) hk
    convert hk' using 1 <;>
      simp only [mvfderiv, ContinuousLinearMap.coe_comp,
        Function.comp_apply, map_zero]; rfl
  have hs := D.regularLevel_sectionalCurvature_lower_bound
    hf U hreg t (K (incl z)) β hβ gL.leviCivitaData z
    (fun a b _ _ _ => hsec (incl z) z.2 a b)
    (fun w => hhess (incl z) z.2 _ (htan w)) u v hu hv huv
  simpa only [E, Function.comp_apply, PoincareConjecture.LeviCivitaData.levelSectionalError,
    neg_add_rev, sub_eq_add_neg, add_comm] using hs
