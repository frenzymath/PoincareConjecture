import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Selected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialGauss







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] [ConnectedSpace M] [IsManifold (𝓡 n) ∞ M] in

theorem curve_velocity_comp {γ : ℝ → M} {f : ℝ → ℝ} {t c : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (f t)) (hf : HasDerivAt f c t) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ ∘ f) t 1 =
      c • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (f t) 1 := by
  have hd := mfderiv_comp t hγ hf.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ ∘ f) t 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (f t) (fderiv ℝ f t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul, hf.deriv] at hv
  rw [hv]
  simpa only [smul_eq_mul, mul_one] using
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (f t)).map_smul c (1 : ℝ)



theorem exists_squared_distance_endpoint_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ σ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ σ 0) (hσ0 : σ 0 = γ 1) :
    ∃ u : ℝ → ℝ, u 0 = (g.edist (γ 0) (σ 0)).toReal ^ 2 ∧
      (∀ᶠ s in 𝓝 0, (g.edist (γ 0) (σ s)).toReal ^ 2 ≤ u s) ∧
      HasDerivAt u (2 * g.inner (γ 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) 0 := by
  obtain ⟨R, e, v, B, he, hnorm, hradial, hv, hv0, hx, hvnorm, hmatch,
      hvB, heB, hBi, hmajor⟩ :=
    g.exists_radial_support_on_minimizing_segment D hcomplete hγ hneq hmin
  let d := (g.edist (γ 0) (γ 1)).toReal
  let u := B.symm ∘ σ
  have hxB : B v = σ 0 := (heB hvB).symm.trans (hx.trans hσ0.symm)
  have htB : σ 0 ∈ B.target := hxB ▸ B.map_source hvB
  have hu0 : u 0 = v := by dsimp [u]; rw [← hxB, B.left_inv hvB]
  have hu : ContDiffAt ℝ ∞ u 0 := contMDiffAt_iff_contDiffAt.mp
    ((hBi.contMDiffAt (B.open_target.mem_nhds htB)).comp 0 hσ)
  have hr : ContDiffAt ℝ ∞ (fun s => ‖u s‖) 0 :=
    (contDiffAt_norm ℝ (hu0 ▸ hv0)).comp 0 hu
  have hproj : (e ∘ u) =ᶠ[𝓝 0] σ := by
    filter_upwards [hσ.continuousAt.preimage_mem_nhds (B.open_target.mem_nhds htB)] with s hs
    change e (B.symm (σ s)) = σ s
    rw [heB (B.map_target hs), B.right_inv hs]
  have hev := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp)
  have hvel : mfderiv (𝓡 n) (𝓡 n) e v (deriv u 0) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1 := by
    have hd := mfderiv_comp 0 (hu0 ▸ hev) (hu.differentiableAt (by simp)).mdifferentiableAt
    rw [hproj.mfderiv_eq, mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1 =
      mfderiv (𝓡 n) (𝓡 n) e (u 0) (fderiv ℝ u 0 1) at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hu0] at hd1
    exact hd1.symm
  have hradvel : mfderiv (𝓡 n) (𝓡 n) e v v =
      (1 / 2 : ℝ) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
    have hline : HasDerivAt (fun r : ℝ => r • v) v 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
    have hd := mfderiv_comp 1 (by simpa only [one_smul] using hev)
      hline.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • v)) 1 1 =
      mfderiv (𝓡 n) (𝓡 n) e (1 • v) (fderiv ℝ (fun r : ℝ => r • v) 1 1) at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hline.deriv, one_smul] at hd1
    have hγd := (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ
      (by simp : (1 : ℝ) ∈ Icc 0 1)).mdifferentiableAt (by simp)
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
  have hpair := g.radial_gauss_identity D he hnorm hradial v hv (deriv u 0)
  rw [hvel, hradvel, map_smul, smul_apply, smul_eq_mul] at hpair
  rw [hx] at hpair
  let f : ℝ → ℝ := fun s => (d / 2 + ‖u s‖) ^ 2
  refine ⟨f, ?_, ?_, ?_⟩
  · dsimp [f]
    rw [hu0, hvnorm, hσ0]
    change (d / 2 + d / 2) ^ 2 = d ^ 2
    ring
  · filter_upwards [hσ.continuousAt.preimage_mem_nhds (B.open_target.mem_nhds htB)] with s hs
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hmajor (σ s) hs) 2
  · have hr' := (hr.differentiableAt (by simp)).hasDerivAt
    have hsq := (hu.differentiableAt (by simp)).hasDerivAt.norm_sq
    have heq := (hr'.pow 2).unique hsq
    simp only [hu0] at heq
    norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at heq
    have hf := (hr'.const_add (d / 2)).pow 2
    norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at hf
    convert! hf using 1
    change 2 * g.inner (γ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) =
        2 * (d / 2 + ‖u 0‖) * deriv (fun s => ‖u s‖) 0
    rw [hu0]
    rw [show d / 2 = ‖v‖ from hvnorm.symm]
    nlinarith [heq, hpair]

end PoincareConjecture.RiemannianMetric
