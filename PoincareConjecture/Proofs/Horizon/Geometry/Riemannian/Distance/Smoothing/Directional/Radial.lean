import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Support
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem mvfderiv_endpoint_le_of_hessian_le (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγU : MapsTo γ (Icc 0 1) U) {r C : ℝ}
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = r)
    (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v) :
    mvfderiv (𝓡 n) f (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) ≤
      f (γ 1) - f (γ 0) + C * r ^ 2 / 2 := by
  let F : ℝ → ℝ := f ∘ γ
  let V := fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  let A := fun t => D.hessian f (γ t) (V t) (V t)
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F (deriv F t) t := by
    exact ((contMDiffAt_iff_contDiffAt.mp
      (((hf.contMDiffAt (hU.mem_nhds (hγU ht))).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp t
        (hγ.contMDiffAt ht))).differentiableAt (by simp)).hasDerivAt
  have hsecond (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (deriv F) (A t) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU hf hγ ht (hγU ht)
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : A t ≤ C * r ^ 2 := by
    have hsq : g.inner (γ t) (V t) (V t) = r ^ 2 := by
      have hs := congrArg (fun s : ℝ => s ^ 2) (hspeed t ht)
      change (Real.sqrt (g.inner (γ t) (V t) (V t))) ^ 2 = r ^ 2 at hs
      have hnonneg : 0 ≤ g.inner (γ t) (V t) (V t) := by
        by_cases hv : V t = 0
        · simp [hv]
        · exact (g.pos (γ t) (V t) hv).le
      rw [Real.sq_sqrt hnonneg] at hs
      exact hs
    simpa only [A, hsq] using hhess t ht (V t)
  have hreverse (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hrev : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => F (1 - s)) (-deriv F (1 - t)) t := by
    intro t ht
    simpa only [Function.comp_def, mul_neg_one] using
      (hfirst (1 - t) (hreverse t ht)).comp t ((hasDerivAt_id t).const_sub 1)
  have hrev' : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => -deriv F (1 - s)) (A (1 - t)) t := by
    intro t ht
    convert! ((hsecond (1 - t) (hreverse t ⟨ht.1.le, ht.2.le⟩)).comp t
      ((hasDerivAt_id t).const_sub 1)).neg using 1
    simp only [mul_neg_one, neg_neg]
  have hbound := Poincare.Analysis.quadratic_upper_bound_of_hasDerivAt2_le
    (by norm_num : (0 : ℝ) ≤ 1) hrev hrev'
    (fun t ht => hA (1 - t) (hreverse t ⟨ht.1.le, ht.2.le⟩))
  have hdu : deriv F 1 =
      mvfderiv (𝓡 n) f (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) := by
    have heq := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp 1 ((hf.contMDiffAt (hU.mem_nhds (hγU (by simp)))).mdifferentiableAt
        (by simp)) ((hγ.contMDiffAt (by simp)).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    exact heq
  simp only [sub_self, sub_zero, one_mul, one_pow] at hbound
  rw [← hdu]
  change F 0 ≤ F 1 + -deriv F 1 + C * r ^ 2 * 1 / 2 at hbound
  change deriv F 1 ≤ F 1 - F 0 + C * r ^ 2 / 2
  linarith

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_distance_radial_upper_support_on_minimizing_segment
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ γ 1 ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal ∧
      (∀ y ∈ U, (g.edist (γ 0) y).toReal ≤ rho y) ∧
      D.gradient rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal⁻¹ •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 ∧
      g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient rho (γ 1)) = 1 := by
  obtain ⟨R, e, v, B, he, hnorm, hradial, hv, hv0, hx, hvnorm, hmatch,
      hvB, heB, hBi, hmajor⟩ :=
    g.exists_radial_support_on_minimizing_segment D hcomplete hγ hneq hmin
  let d := (g.edist (γ 0) (γ 1)).toReal
  have hd : 0 < d := by
    let := g.toMetricSpace
    exact dist_pos.mpr hneq
  let Ω : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 R ∩ {z | z ≠ 0}
  have hΩ : IsOpen Ω := Metric.isOpen_ball.inter (isClosed_singleton.isOpen_compl)
  let B' := B.restrOpen Ω hΩ
  have hvB' : v ∈ B'.source := ⟨hvB, hv, hv0⟩
  have hBe : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B' B'.source := by
    intro z hz
    have hez := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hz.2.1)
    apply (hez.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [B.open_source.mem_nhds hz.1] with w hw
    exact (heB hw).symm
  have hBi' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B'.symm B'.target :=
    hBi.mono (fun _ hy => hy.1)
  have hxB : B' v = γ 1 := (heB hvB).symm.trans hx
  have hxmem : γ 1 ∈ B'.target := hxB ▸ B'.map_source hvB'
  have hnormB : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ‖B'.symm y‖) B'.target := by
    intro y hy
    exact (((contDiffAt_norm ℝ hy.2.2 (n := ∞)).contMDiffAt).comp y
      (hBi'.contMDiffAt (B'.open_target.mem_nhds hy))).contMDiffWithinAt
  have hlocal : e =ᶠ[𝓝 v] B' :=
    Filter.eventuallyEq_of_mem (B.open_source.mem_nhds hvB) heB
  have hgauss := g.radial_gauss_identity D he hnorm hradial v hv
  have hgaussB : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (B' v) (mfderiv (𝓡 n) (𝓡 n) B' v v)
        (mfderiv (𝓡 n) (𝓡 n) B' v w) = inner ℝ v w := by
    intro w
    have hg := hgauss w
    rw [hlocal.mfderiv_eq] at hg
    change g.inner (e v)
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) B' v v)
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) B' v w) = _ at hg
    rw [hlocal.self_of_nhds] at hg
    exact hg
  have hev := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp)
  have hradvel : mfderiv (𝓡 n) (𝓡 n) e v v =
      (1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
    have hline : HasDerivAt (fun r : ℝ => r • v) v 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
    have hdline := mfderiv_comp 1 (by simpa only [one_smul] using hev)
      hline.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hdline
    have hd1 := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hdline
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) 1 1 =
      mfderiv (𝓡 n) (𝓡 n) e (1 • v) (fderiv ℝ (fun r : ℝ => r • v) 1 1) at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hline.deriv, one_smul] at hd1
    have hγd := (hγ.contMDiffAt (by simp : (1 : ℝ) ∈ Icc 0 1)).mdifferentiableAt
      (by simp)
    have haff : HasDerivAt (fun r : ℝ => r / 2 + 1 / 2) (1 / 2) 1 := by
      convert! ((hasDerivAt_id (1 : ℝ)).div_const 2).add_const (1 / 2) using 1
    have hcomp := curve_velocity_comp (by norm_num; exact hγd) haff
    have hmaps : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) 1 =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => γ (r / 2 + 1 / 2)) 1 :=
      hmatch.mfderiv_eq
    have hm := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hmaps
    have hg1 := congrArg (fun t : ℝ =>
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
      (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    exact hd1.symm.trans (hm.trans (hcomp.trans
      (congrArg (fun z : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) • z) hg1)))
  let rho : M → ℝ := fun y => d / 2 + ‖B'.symm y‖
  have hgrad : D.gradient rho (γ 1) =
      d⁻¹ • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
    rw [show D.gradient rho (γ 1) = D.gradient (fun y => ‖B'.symm y‖) (γ 1) from
      D.gradient_const_add_at ((hnormB.contMDiffAt
        (B'.open_target.mem_nhds hxmem)).mdifferentiableAt (by simp)) (d / 2)]
    have hg := D.gradient_radial_coordinate B' hBe hBi' hvB' hv0 hgaussB
    have hradB : (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) B' v v) =
        (1 / 2 : ℝ) • (show EuclideanSpace ℝ (Fin n) from
          mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) := by
      rw [← hlocal.mfderiv_eq]
      exact hradvel
    calc
      D.gradient (fun y => ‖B'.symm y‖) (γ 1) =
          mfderiv (𝓡 n) (𝓡 n) B' v (‖v‖⁻¹ • v) := by
        change (show EuclideanSpace ℝ (Fin n) from
          D.gradient (fun y => ‖B'.symm y‖) (B' v)) =
          (show EuclideanSpace ℝ (Fin n) from
            mfderiv (𝓡 n) (𝓡 n) B' v (‖v‖⁻¹ • v)) at hg
        rw [hxB] at hg
        exact hg
      _ = ‖v‖⁻¹ • (show EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) (𝓡 n) B' v v) := by rw [map_smul]
      _ = d⁻¹ • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
        rw [hradB, smul_smul, hvnorm]
        congr 1
        dsimp only [d]
        field_simp
  refine ⟨B'.target, rho, B'.open_target, hxmem,
    contMDiffOn_const.add hnormB, ?_, fun y hy => hmajor y hy.1, hgrad, ?_⟩
  · dsimp only [rho]
    rw [show B'.symm (γ 1) = v by rw [← hxB, B'.left_inv hvB'], hvnorm]
    change d / 2 + d / 2 = d
    ring
  · have hu := D.inner_gradient_radial_coordinate B' hBe hBi' hvB' hv0 hgaussB
    rw [hxB] at hu
    simpa only [rho, D.gradient_const_add_at ((hnormB.contMDiffAt
      (B'.open_target.mem_nhds hxmem)).mdifferentiableAt (by simp))] using hu

theorem exists_distance_upper_support_gradient_pairing_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    {V : Set M} (hV : IsOpen V) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f V) (hγV : MapsTo γ (Icc 0 1) V)
    {C : ℝ} (hhess : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      D.hessian f (γ t) v v ≤ C * g.inner (γ t) v v) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ γ 1 ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal ∧
      (∀ y ∈ U, (g.edist (γ 0) y).toReal ≤ rho y) ∧
      D.gradient rho (γ 1) = (g.edist (γ 0) (γ 1)).toReal⁻¹ •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 ∧
      g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient rho (γ 1)) = 1 ∧
      g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient f (γ 1)) ≤
        (f (γ 1) - f (γ 0)) / (g.edist (γ 0) (γ 1)).toReal +
          C * (g.edist (γ 0) (γ 1)).toReal / 2 := by
  obtain ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit⟩ :=
    g.exists_distance_radial_upper_support_on_minimizing_segment D hcomplete hγ hneq hmin
  let d := (g.edist (γ 0) (γ 1)).toReal
  have hd : 0 < d := by
    let := g.toMetricSpace
    exact dist_pos.mpr hneq
  have hsq : g.inner (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) = d ^ 2 := by
    simp only [hgrad, map_smul, smul_apply, smul_eq_mul] at hunit
    change d⁻¹ * (d⁻¹ * _) = 1 at hunit
    field_simp [hd.ne'] at hunit
    nlinarith
  have hspeed1 : g.tangentNorm (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) = d := by
    change Real.sqrt _ = d
    rw [hsq, Real.sqrt_sq hd.le]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = d := by
    have hc := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hγ.hasDerivAt_tangentNorm_zero hs).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ))) (by simp : (1 : ℝ) ∈ Icc 0 1) ht
    have heq : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) =
        g.tangentNorm (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1) := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hc
    exact heq.trans hspeed1
  have hbound := D.mvfderiv_endpoint_le_of_hessian_le hV hf hγ hγV hspeed hhess
  refine ⟨U, rho, hU, hxU, hrho, htouch, hupper, hgrad, hunit, ?_⟩
  rw [hgrad, map_smul, smul_apply, smul_eq_mul, g.symm,
    D.inner_gradient]
  change d⁻¹ * _ ≤ (f (γ 1) - f (γ 0)) / d + C * d / 2
  calc
    _ ≤ d⁻¹ * (f (γ 1) - f (γ 0) + C * d ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hd.le)
    _ = (f (γ 1) - f (γ 0)) / d + C * d / 2 := by field_simp

end PoincareConjecture.RiemannianMetric
