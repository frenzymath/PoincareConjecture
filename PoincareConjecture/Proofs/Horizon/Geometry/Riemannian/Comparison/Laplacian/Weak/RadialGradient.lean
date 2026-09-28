import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.CutLocus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.RadialSpeed

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_eq_velocity_of_calibrated_curve (D : LeviCivitaData g)
    {f : M → ℝ} (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ t)
    (hspeed : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hcal : HasDerivAt (fun s => f (γ s)) 1 t) :
    D.gradient f (γ t) = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm := D.gradient_norm_le_of_distance_lipschitz (by norm_num : (0 : ℝ) ≤ 1)
    (fun x y => by simpa only [one_mul] using hLip x y) hf
  have hd := (hf.hasMFDerivAt.comp t hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun s => f (γ s))
    (mvfderiv (𝓡 n) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) t at hd
  have hinner := hd.unique hcal
  rw [← D.inner_gradient] at hinner
  let u := D.gradient f (γ t)
  let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  change ‖u‖ ≤ 1 at hnorm
  change ‖v‖ = 1 at hspeed
  change inner ℝ u v = 1 at hinner
  have hinner' : inner ℝ v u = 1 := (real_inner_comm _ _).trans hinner
  have hsub : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
      hinner, hinner', hspeed]
    ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg u, norm_nonneg (u - v), sq_nonneg (‖u - v‖)]

theorem mvfderiv_distance_gradient_eq_deriv_of_calibrated_curve
    [T3Space M] [PreconnectedSpace M] (D : LeviCivitaData g) (p : M)
    {γ : ℝ → M} {t : ℝ} (ht : 0 < t)
    (hd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun x => (g.edist p x).toReal) (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ t)
    (hspeed : g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hcal : ∀ᶠ s in 𝓝 t, g.edist p (γ s) = ENNReal.ofReal s)
    {φ : M → ℝ} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ (γ t)) :
    mvfderiv (𝓡 n) (fun x => (g.edist p x).toReal) (γ t)
      (D.gradient φ (γ t)) = deriv (fun s => φ (γ s)) t := by
  have hc : HasDerivAt (fun s => (g.edist p (γ s)).toReal) 1 t := by
    apply (hasDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [hcal, Ioi_mem_nhds ht] with s hs hspos
    rw [hs, ENNReal.toReal_ofReal hspos.le]
    rfl
  have hgrad := D.gradient_eq_velocity_of_calibrated_curve
    (g.abs_toReal_edist_sub_le p) hd hγ hspeed hc
  have hderiv := (hφ.hasMFDerivAt.comp t hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun s => φ (γ s))
    (mvfderiv (𝓡 n) φ (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) t at hderiv
  rw [← D.inner_gradient, hgrad, g.symm, D.inner_gradient, hderiv.deriv]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

open Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem eventually_edist_radial_eq_of_nonterminal
    (g : RiemannianMetric n M) {p : M} {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (s • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) s 1) = ‖v‖)
    (hdist : ∀ v ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
      g.edist p (e (s • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal s)
    {θ : EuclideanSpace ℝ (Fin n)} (hθ : ‖θ‖ = 1)
    {t : ℝ} (ht : 0 < t)
    (htS : t • θ ∈ localMinimizingSet (fun v => g.edist p (e v)) R \
      terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R) :
    ∀ᶠ s in 𝓝 t, g.edist p (e (s • θ)) = ENNReal.ofReal s := by
  have hnorm : ‖t • θ‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, hθ, mul_one]
  have hne : t • θ ≠ 0 := by
    intro h
    have hh := congrArg norm h
    rw [hnorm, norm_zero] at hh
    exact ht.ne' hh
  obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧
      (q : ℝ) * ‖t • θ‖ < R ∧ (q : ℝ) • (t • θ) ∈
        localMinimizingSet (fun v => g.edist p (e v)) R := by
    by_contra h
    exact htS.2 ⟨htS.1, hne, mem_iInter.mpr (fun q hq => h ⟨q, hq⟩)⟩
  have hqt : t < (q : ℝ) * t := by nlinarith
  have hqtpos : 0 < (q : ℝ) * t := ht.trans hqt
  filter_upwards [Ioo_mem_nhds ht hqt] with s hs
  have ha0 : 0 ≤ s / ((q : ℝ) * t) := div_nonneg hs.1.le hqtpos.le
  have ha1 : s / ((q : ℝ) * t) ≤ 1 := (div_le_one hqtpos).mpr hs.2.le
  have hsS := radial_minimizing_star g he hqS (hspeed _ hqS.1)
    (hdist _ hqS.1) _ ha0 ha1
  have hscale : (s / ((q : ℝ) * t)) • ((q : ℝ) • (t • θ)) = s • θ := by
    rw [smul_smul, smul_smul, div_mul_eq_div_mul_one_div]
    field_simp
  rw [hscale] at hsS
  have hn : ‖s • θ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs.1.le, hθ, mul_one]
  simpa only [mem_ofPred_eq, hn] using hsS.2

theorem mvfderiv_distance_gradient_eq_radial_deriv
    [PreconnectedSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M} {R : ℝ}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (s • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) s 1) = ‖v‖)
    (hdist : ∀ v ∈ Metric.ball 0 R, ∀ s ∈ Icc (0 : ℝ) 1,
      g.edist p (e (s • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal s)
    {θ : EuclideanSpace ℝ (Fin n)} (hθ : ‖θ‖ = 1)
    {t : ℝ} (ht : 0 < t)
    (htS : t • θ ∈ localMinimizingSet (fun v => g.edist p (e v)) R \
      terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R)
    (hd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun x => (g.edist p x).toReal) (e (t • θ)))
    {φ : M → ℝ} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ (e (t • θ))) :
    mvfderiv (𝓡 n) (fun x => (g.edist p x).toReal) (e (t • θ))
      (D.gradient φ (e (t • θ))) = deriv (fun s => φ (e (s • θ))) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hed := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds htS.1.1)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hline : HasDerivAt (fun s : ℝ => s • θ) θ t := by
    simpa using (hasDerivAt_id t).smul_const θ
  have hγ := hed.comp t hline.differentiableAt.mdifferentiableAt
  have hv : g.tangentNorm (e (t • θ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • θ)) t 1) = 1 := by
    rw [radial_velocity_eq_differential θ hed]
    have hs := hspeed (t • θ) htS.1.1 1 (by simp)
    rw [← g.tangentNorm_mfderiv_radial_eq hed] at hs
    change ‖mfderiv (𝓡 n) (𝓡 n) e (t • θ) (t • θ)‖ = ‖t • θ‖ at hs
    rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, hθ, mul_one] at hs
    change ‖mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ‖ = 1
    nlinarith
  exact D.mvfderiv_distance_gradient_eq_deriv_of_calibrated_curve p ht hd hγ hv
    (g.eventually_edist_radial_eq_of_nonterminal he hspeed hdist hθ ht htS) hφ

end PoincareConjecture.RiemannianMetric
