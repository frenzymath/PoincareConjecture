import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Tail
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Radial
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

private theorem second_deriv_sq {r : ℝ → ℝ} {t : ℝ}
    (hr : ContDiffAt ℝ 2 r t) :
    deriv (deriv (fun s => r s ^ 2)) t =
      2 * deriv r t ^ 2 + 2 * r t * deriv (deriv r) t := by
  have hfirst : deriv (fun s => r s ^ 2) =ᶠ[𝓝 t]
      (fun s => 2 * r s * deriv r s) := by
    filter_upwards [hr.eventually (by norm_num)] with s hs
    convert! ((hs.differentiableAt (by norm_num)).hasDerivAt.pow 2).deriv using 1
    simp
  have hrd : DifferentiableAt ℝ (deriv r) t :=
    (hr.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (((hr.differentiableAt (by norm_num)).hasDerivAt.const_mul 2).mul
    hrd.hasDerivAt).deriv
  change deriv (fun s => 2 * r s * deriv r s) t =
    2 * deriv r t * deriv r t + 2 * r t * deriv (deriv r) t at hd
  rw [hfirst.deriv_eq, hd]
  ring

private theorem second_deriv_shifted_sq_le {r : ℝ → ℝ} {t l C : ℝ}
    (hr : ContDiffAt ℝ 2 r t) (hrpos : 0 < r t) (hl : 0 ≤ l)
    (hbound : deriv (deriv (fun s => r s ^ 2)) t ≤ 2 * C) :
    deriv (deriv (fun s => (l + r s) ^ 2)) t ≤ 2 * (1 + l / r t) * C := by
  rw [second_deriv_sq hr] at hbound
  have hshift := second_deriv_sq ((contDiffAt_const (c := l)).add hr)
  simp only [deriv_const_add'] at hshift
  rw [hshift]
  apply (mul_le_mul_iff_of_pos_right hrpos).mp
  have heq : (2 * (1 + l / r t) * C) * r t = 2 * (r t + l) * C := by
    field_simp [ne_of_gt hrpos]
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hbound (add_nonneg hrpos.le hl)
  nlinarith [mul_nonneg hl (sq_nonneg (deriv r t))]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem deriv2_shifted_inverse_radius_sq_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    {e : EuclideanSpace ℝ (Fin n) → M} {R l : ℝ} (hl : 0 ≤ l)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v)) {r : ℝ | r • v ∈ Metric.ball 0 R})
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hvB : v ∈ B.source)
    (hv0 : v ≠ 0) (hi : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible)
    (hmin : g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖)
    {γ : ℝ → M} {I : Set ℝ} {t : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hx : e v = γ t) :
    deriv (deriv (fun s => (l + ‖B.symm (γ s)‖) ^ 2)) t ≤
      2 * (1 + l / ‖v‖) *
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
  let u := B.symm ∘ γ
  have hxB : B v = γ t := (heB hvB).symm.trans hx
  have htB : γ t ∈ B.target := hxB ▸ B.map_source hvB
  have hut : u t = v := by dsimp [u]; rw [← hxB, B.left_inv hvB]
  have hγt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ ht
  have hu : ContDiffAt ℝ ∞ u t := contMDiffAt_iff_contDiffAt.mp
    ((hBi.contMDiffAt (B.open_target.mem_nhds htB)).comp t hγt)
  have hproj : (e ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hγt.continuousAt.preimage_mem_nhds (B.open_target.mem_nhds htB)] with s hs
    change e (B.symm (γ s)) = γ s
    rw [heB (B.map_target hs), B.right_inv hs]
  have het : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (u t) := by
    rw [hut]
    exact he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)
  have hit : (mfderiv (𝓡 n) (𝓡 n) e (u t)).IsInvertible := hut ▸ hi
  have hode := g.deriv2_lift_eq_neg_christoffel het hit.bijective hu hγ ht hproj
  have hbound := Toponogov.deriv2_norm_sq_le_of_minimizing_radial g D hsec he hnorm hradial
    (hut ▸ hv) (hut ▸ hv0) hit.bijective (hut ▸ hmin)
    (hu.of_le (by norm_cast)) hode
  rw [g.pullback_velocity_inner_eq_of_lift (het.mdifferentiableAt (by simp))
    (hu.differentiableAt (by simp)) hproj] at hbound
  have hr : ContDiffAt ℝ 2 (fun s => ‖u s‖) t :=
    ((contDiffAt_norm ℝ (hut ▸ hv0)).comp t hu).of_le (by norm_cast)
  have h := second_deriv_shifted_sq_le hr (by rw [hut]; exact norm_pos_iff.mpr hv0) hl hbound
  rw [hut] at h
  exact h

variable [T3Space M] [ConnectedSpace M]

theorem exists_squared_distance_upper_support_of_shift
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {γ : ℝ → M} {I : Set ℝ} {t δ : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hpx : p ≠ γ t)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧
      u t = (g.edist p (γ t)).toReal ^ 2 ∧
      (∀ᶠ s in 𝓝 t, (g.edist p (γ s)).toReal ^ 2 ≤ u s) ∧
      deriv (deriv u) t ≤ 2 / (1 - δ) *
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
  obtain ⟨ε, η, R, L, e, v, B, hε, hη, hη0, hη1, hηmin, hR, hdR,
      hL, hnorm, he, he0, hed, hradial, hv, hv0, hx, hvnorm, hsplit,
      hleft, hmin, hi, hvB, hBU, heB, hB, hBi, hzero, hnormB, hmajor⟩ :=
    g.exists_smooth_radial_inverse_branch_of_shift D hcomplete p (γ t) hpx hδ hδhalf
  let d := (g.edist p (γ t)).toReal
  have hd : 0 < d := by
    have := norm_pos_iff.mpr hv0
    rw [hvnorm] at this
    dsimp [d]
    nlinarith [ENNReal.toReal_nonneg (a := g.edist p (γ t))]
  have hxB : B v = γ t := (heB hvB).symm.trans hx
  have htB : γ t ∈ B.target := hxB ▸ B.map_source hvB
  have hγt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ ht
  have hnormt : ‖B.symm (γ t)‖ = (1 - δ) * d := by
    rw [← hxB, B.left_inv hvB]
    exact hvnorm
  let u : ℝ → ℝ := fun s => (δ * d + ‖B.symm (γ s)‖) ^ 2
  have hu : ContDiffAt ℝ 2 u t := by
    have hr := (hnormB.contMDiffAt (B.open_target.mem_nhds htB)).comp t hγt
    exact ((contDiffAt_const.add (contMDiffAt_iff_contDiffAt.mp hr)).pow 2).of_le
      (by norm_cast)
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · dsimp [u]
    rw [hnormt]
    change (δ * d + (1 - δ) * d) ^ 2 = d ^ 2
    ring
  · filter_upwards [hγt.continuousAt.preimage_mem_nhds
      (B.open_target.mem_nhds htB)] with s hs
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hmajor (γ s) hs) 2
  · have hi1 : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
      have h := hi 1 (by simp)
      rw [one_smul] at h
      exact h
    have h := g.deriv2_shifted_inverse_radius_sq_le D hsec
      (mul_nonneg hδ.le hd.le) he hnorm (fun w hw => (hradial w hw).1)
      B heB hBi hv hvB hv0 hi1 hmin hγ ht hx
    have hcoef : 2 * (1 + δ * d / ‖v‖) = 2 / (1 - δ) := by
      rw [hvnorm]
      change 2 * (1 + δ * d / ((1 - δ) * d)) = 2 / (1 - δ)
      field_simp [ne_of_gt hd, show 1 - δ ≠ 0 by linarith]
      ring
    rw [hcoef] at h
    exact h

theorem exists_squared_distance_upper_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {γ : ℝ → M} {I : Set ℝ} {t : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hpx : p ≠ γ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℝ, ContDiffAt ℝ 2 u t ∧
      u t = (g.edist p (γ t)).toReal ^ 2 ∧
      (∀ᶠ s in 𝓝 t, (g.edist p (γ s)).toReal ^ 2 ≤ u s) ∧
      deriv (deriv u) t ≤ 2 *
        g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) + ε := by
  let C := g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
  have hC : 0 ≤ C := by
    by_cases hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 = 0
    · simp [C, hv]
    · exact (g.pos _ _ hv).le
  let δ := min (1 / 4 : ℝ) (ε / (4 * (C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδquarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : δ * (4 * (C + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp (min_le_right _ _)
  obtain ⟨u, hu, htouch, hmajor, hbound⟩ :=
    g.exists_squared_distance_upper_support_of_shift D hcomplete hsec p hγ ht hpx
      hδ (by linarith)
  refine ⟨u, hu, htouch, hmajor, hbound.trans ?_⟩
  change 2 / (1 - δ) * C ≤ 2 * C + ε
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).mpr
  nlinarith [mul_nonneg hC hδ.le, mul_le_mul_of_nonneg_left hδquarter hε.le]

end PoincareConjecture.RiemannianMetric
