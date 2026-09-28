import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.TerminalRigidity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.AncientVolume.ScalarRatio

private theorem second_derivative_of_quadratic_interpolation
    {F : ℝ → ℝ} {a c : ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ F t)
    (hsecond : HasDerivAt (deriv F) a 0)
    (hquad : ∀ t ∈ Icc (0 : ℝ) 1,
      F t = (1 - t) * F 0 + t * F 1 - t * (1 - t) * c / 2) : a = c := by
  let b := F 1 - F 0 - c / 2
  let P : ℝ → ℝ := fun t => F 0 + t * b + t ^ 2 * c / 2
  have hvalue : EqOn F P (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hquad t ht]
    dsimp [P, b]
    ring
  have hP (t : ℝ) : HasDerivAt P (b + t * c) t := by
    convert! (((hasDerivAt_const t (F 0)).add ((hasDerivAt_id t).mul_const b)).add
      (((hasDerivAt_id t).pow 2).mul_const c |>.div_const 2)) using 1
    dsimp [P]
    ring
  have hderiv : EqOn (deriv F) (fun t => b + t * c) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hwithin := (hP t).hasDerivWithinAt.congr hvalue (hvalue ht)
    exact ((hF t ht).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)).symm.trans
        (hwithin.derivWithin (uniqueDiffOn_Icc_zero_one t ht))
  have hPsecond : HasDerivAt (fun t : ℝ => b + t * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add b
  exact (uniqueDiffOn_Icc_zero_one 0 (by simp)).eq_deriv (Icc (0 : ℝ) 1)
    hsecond.hasDerivWithinAt
    (hPsecond.hasDerivWithinAt.congr hderiv (hderiv (by simp)))

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_deriv_comp_geodesic
    (D : LeviCivitaData g) {f : M → ℝ} {γ : ℝ → M} {s : Set ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) t := by
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  let c := extChartAt (𝓡 n) p
  let F := f ∘ c.symm
  have hF (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target) :
      ContDiffAt ℝ ∞ F x := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hf (c.symm x)).comp x
      ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hx).contMDiffAt
        (extChartAt_target_mem_nhds' hx))
  have hfirst : ∀ᶠ u in 𝓝 t,
      HasDerivAt (f ∘ γ) (fderiv ℝ F (q u) (w u)) u := by
    filter_upwards [hlocal, hlocal.eventually_nhds] with u hu hue
    have hd := ((hF (q u) hu.2.1).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt u hu.2.2.1
    apply hd.congr_of_eventuallyEq
    filter_upwards [hue] with v hv
    exact congrArg f hv.1
  have hqt := hlocal.self_of_nhds
  have hsecond := (((hF (q t) hqt.2.1).fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hqt.2.2.1
  have hfield := hsecond.clm_apply hqt.2.2.2
  have hH := D.hessian_in_chart p hqt.2.1 (hf _) (w t) (w t)
  have hfieldH : HasDerivAt (deriv (f ∘ γ))
      (D.hessian f (c.symm (q t))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (w t))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (w t))) t := by
    rw [hH]
    have hd : HasDerivAt (fun u => fderiv ℝ F (q u) (w u))
        (fderiv ℝ (fderiv ℝ F) (q t) (w t) (w t) -
          fderiv ℝ F (q t)
            (CoordinateExponential.christoffelBilinear
              (g.pullbackCoefficients c.symm) (q t) (w t) (w t))) t := by
      simpa +instances only [Function.comp_def, map_neg, ← sub_eq_add_neg,
        CoordinateExponential.christoffelBilinear_apply] using hfield
    exact hd.congr_of_eventuallyEq (hfirst.mono fun _ hu => hu.deriv)
  have hcurve : γ =ᶠ[𝓝 t] fun u => c.symm (q u) := hlocal.mono fun _ hu => hu.1
  have hc := ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hqt.2.1).contMDiffAt
    (extChartAt_target_mem_nhds' hqt.2.1)).mdifferentiableAt (by simp)
  have hv := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp t hc hqt.2.2.1.differentiableAt.mdifferentiableAt)
  rw [mfderiv_eq_fderiv] at hv
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u => c.symm (q u)) t 1 =
    mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (deriv q t) at hv
  rw [hqt.2.2.1.deriv] at hv
  rw [hcurve.mfderiv_eq, hcurve.self_of_nhds, hv]
  exact hfieldH

private theorem hessian_diagonal_of_unit_geodesic_quadratic
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2))
    {p : M} (hp : γ 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    (hquad : ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2) :
    D.hessian f p v v = g.inner p v v := by
  subst p
  have hγd := (hγ.contMDiffAt (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num)).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hchart := mdifferentiableAt_extChartAt (I := 𝓡 n) (mem_chart_source _ (γ 0))
  have heq := congrArg (fun L => L (1 : ℝ)) (mfderiv_comp 0 hchart hγd)
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun t => extChartAt (𝓡 n) (γ 0) (γ t)) 0 = _ at heq
  rw [hv.deriv, mfderiv_extChartAt_self] at heq
  change v = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 at heq
  have hdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℝ (f ∘ γ) t := by
    have ht' : t ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hfs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 f (γ t) := (hf _).of_le (by simp)
    exact (contMDiffAt_iff_contDiffAt.mp (hfs.comp t (hγ.contMDiffAt ht'))).differentiableAt
      (by norm_num)
  have h := Poincare.AncientVolume.ScalarRatio.second_derivative_of_quadratic_interpolation
    hdiff (D.hasDerivAt_deriv_comp_geodesic hf hγ (by norm_num)) hquad
  rw [← heq] at h
  have hnonneg : 0 ≤ g.inner (γ 0) v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact (g.pos (γ 0) v hv0).le
  simpa only [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] using h

theorem hessian_eq_metric_of_geodesic_quadratic
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = g.inner x u v := by
  have hdiag (w : TangentSpace (𝓡 n) x) : D.hessian f x w w = g.inner x w w := by
    obtain ⟨δ, hδ, _, γ, hγ, hp, hw⟩ := g.exists_geodesic_initial_data x w
    let a : ℝ := δ / 2
    have ha : 0 < a := by dsimp [a]; positivity
    let η : ℝ → M := fun t => γ (a * t)
    have hη : g.IsGeodesicOn η (Ioo (-1 : ℝ) 2) := by
      intro t ht
      apply hγ.comp_mul a t
      change -δ < a * t ∧ a * t < δ
      dsimp [a]
      constructor <;> nlinarith [ht.1, ht.2]
    have hη0 : η 0 = x := by simpa only [η, mul_zero] using hp
    have hηw : HasDerivAt (fun t => extChartAt (𝓡 n) x (η t)) (a • w) 0 := by
      have hw' : HasDerivAt (fun t => extChartAt (𝓡 n) x (γ t)) w (a * 0) := by
        simpa only [mul_zero] using hw
      simpa only [η, Function.comp_def, id_eq, mul_one] using!
        hw'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul a)
    have h := D.hessian_diagonal_of_unit_geodesic_quadratic hf hη hη0 hηw
      (hquad η 1 (by norm_num) (by convert! hη using 1; norm_num))
    rw [D.hessian_eq_inner_connection_gradient (hf x)] at h ⊢
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ ha.ne' (mul_left_cancel₀ ha.ne' h)
  have hsum := hdiag (u + v)
  have hu := hdiag u
  have hv := hdiag v
  have hs := D.hessian_symm hf x u v
  have hgs := g.symm x u v
  simp only [D.hessian_eq_inner_connection_gradient (hf x), map_add,
    add_apply] at hsum hu hv hs ⊢
  linarith

theorem gradient_homothetic_of_geodesic_quadratic
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.gradient f)) ∧
      ∀ x, ∀ v : TangentSpace (𝓡 n) x, D.connection (D.gradient f) x v = v := by
  refine ⟨D.contMDiff_gradient hf, ?_⟩
  intro x v
  apply (g.inner_isInvertible x).injective
  ext w
  rw [← D.hessian_eq_inner_connection_gradient (hf x)]
  exact D.hessian_eq_metric_of_geodesic_quadratic hf hquad x v w

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

universe u

theorem curvatureTensorNorm_eq_zero_of_terminal_geodesic_quadratic
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hquad : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε →
      (F.metric 0).IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        (F.metric 0).tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2) :
    ∀ x, (F.connection 0).curvatureTensorNorm x = 0 := by
  obtain ⟨hsmooth, hgrad⟩ := (F.connection 0).gradient_homothetic_of_geodesic_quadratic hf hquad
  apply curvatureTensorNorm_eq_zero_of_terminal_homothetic_field hC F hoperator
    ((F.connection 0).gradient f) hsmooth (c := 1) (by norm_num)
  intro x v
  simpa only [one_smul] using hgrad x v

end PoincareConjecture.RicciFlow
