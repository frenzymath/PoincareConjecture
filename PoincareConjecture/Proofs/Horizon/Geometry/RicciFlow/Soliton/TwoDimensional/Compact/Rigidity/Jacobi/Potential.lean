import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Jacobi.NoInteriorZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

omit [T2Space M] [PreconnectedSpace M] [IsManifold (𝓡 2) ∞ M] in

theorem deriv_comp_eq_mvfderiv_velocity
    {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t) :
    deriv (f ∘ γ) t = mvfderiv (𝓡 2) f (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) := by
  have hd := congrArg (fun L => L (1 : ℝ)) (mfderiv_comp t hf hγ)
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (f ∘ γ) t 1 = mvfderiv (𝓡 2) f (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) at hd
  simpa only [fderiv_eq_smul_deriv, one_smul] using hd

theorem deriv_potential_ne_zero_inside_minimizing (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    {γ : ℝ → M} {ε C c : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hgeo : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hspeed : ∀ t ∈ Ioo (-ε) (1 + ε),
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) = C)
    (hmin : g.edist (γ 0) (γ 1) = ENNReal.ofReal C)
    (hcrit : D.gradient f (γ 0) = 0) (hR : D.scalarCurvature (γ 0) ≠ 2 * lambda)
    (hc : c ∈ Ioo (0 : ℝ) 1) : deriv (f ∘ γ) c ≠ 0 := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hF : ContDiffOn ℝ ∞ (f ∘ γ) (Ioo (-ε) (1 + ε)) := by
    intro t ht
    exact (contMDiffAt_iff_contDiffAt.mp ((hfs (γ t)).comp t
      (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht))).contDiffWithinAt
  have hφ : ContDiffOn ℝ ∞ (deriv (f ∘ γ)) (Ioo (-ε) (1 + ε)) := by
    intro t ht
    exact (((hF.contDiffAt (isOpen_Ioo.mem_nhds ht)).fderiv_right (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  apply D.scalar_jacobi_ne_zero_of_minimizing hε hC hgeo hspeed hmin hφ
  · intro t ht
    exact (D.hasDerivAt_second_deriv_potential_geodesic hf hsol isOpen_Ioo hgeo
      hspeed (by constructor <;> linarith [ht.1, ht.2])).deriv
  · rw [deriv_comp_eq_mvfderiv_velocity ((hfs (γ 0)).mdifferentiableAt (by simp))
      ((hgeo.contMDiffAt h0).mdifferentiableAt (by simp)), ← D.inner_gradient, hcrit]
    simp
  · rw [(D.hasDerivAt_deriv_potential_geodesic hf hsol hgeo h0 (hspeed 0 h0)).deriv]
    apply mul_ne_zero
    · intro h
      apply hR
      linarith
    · exact pow_ne_zero 2 hC.ne'
  · exact hc

end PoincareConjecture.LeviCivitaData
