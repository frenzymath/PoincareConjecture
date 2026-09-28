import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_quarter_shifted_radial_vector
    (g : RiemannianMetric n M) {p x : M} {ε : ℝ} (hε : 0 < ε)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = x)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p x)
    {R : ℝ} (hR : (g.edist p x).toReal < R)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) (γ (1 / 4))).symm
      (extChartAt (𝓡 n) (γ (1 / 4)) (γ (1 / 4))) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = γ (1 / 4))
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) (γ (1 / 4)) (e v))
      L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R}) :
    ∃ v : EuclideanSpace ℝ (Fin n),
      v ∈ Metric.ball 0 R ∧ ‖v‖ = (3 / 4) * (g.edist p x).toReal ∧ e v = x ∧
      (g.edist p (γ (1 / 4))).toReal + ‖v‖ = (g.edist p x).toReal ∧
      (∀ t ∈ Icc (-1 / 3 : ℝ) 1,
        (fun s : ℝ => e (s • v)) =ᶠ[𝓝 t] (fun s => γ ((3 / 4) * s + 1 / 4))) := by
  let q := γ (1 / 4)
  let η := fun t : ℝ => γ ((3 / 4) * t + 1 / 4)
  have hη : g.IsGeodesicOn η (Ioo (-ε) (1 + ε)) := by
    intro t ht
    exact hγ.comp_affine (3 / 4) (1 / 4) t ⟨by dsimp; linarith [ht.1],
      by dsimp; linarith [ht.2]⟩
  have hη0 : η 0 = q := by dsimp [η, q]; congr 1; ring
  have hη1 : η 1 = x := by simpa only [η, mul_one, show (3 / 4 : ℝ) + 1 / 4 = 1 by ring]
    using hγ1
  have hunit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      (3 / 4) * t + 1 / 4 ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hqx : g.edist q x = ENNReal.ofReal (3 / 4) * g.edist p x := by
    have h := hmin (1 / 4) (by norm_num) 1 (by norm_num)
    norm_num only [hγ1, show (1 / 4 : ℝ) - 1 = -(3 / 4) by ring, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] at h
    exact h
  have hηmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist q x := by
    intro s hs t ht
    dsimp only [η]
    rw [hmin _ (hunit hs) _ (hunit ht), hqx,
      show (3 / 4) * s + 1 / 4 - ((3 / 4) * t + 1 / 4) =
        (3 / 4) * (s - t) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    ring
  let w := deriv (fun t => extChartAt (𝓡 n) q (η t)) 0
  let v := L.symm w
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hw : HasDerivAt (fun t => extChartAt (𝓡 n) q (η t)) w 0 :=
    (hη.hasDerivAt_chart_at h0 q
      (by simpa only [hη0] using mem_extChartAt_source q)).1
  have hLv : L v = w := L.apply_symm_apply w
  have hnorm : g.tangentNorm q w = ‖v‖ := by
    rw [← hLv]
    unfold tangentNorm
    rw [← g.chartCoefficients_self q (L v) (L v), hL,
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]
  have hspeed := hη.initial_tangentNorm_eq_of_edist_segment hε hη0 hw hηmin
  rw [hnorm, hqx] at hspeed
  have hvnorm : ‖v‖ = (3 / 4) * (g.edist p x).toReal := by
    have h := congrArg ENNReal.toReal hspeed
    simpa only [ENNReal.toReal_ofReal (norm_nonneg v), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4)] using h
  have hv : v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, hvnorm]
    have hn := ENNReal.toReal_nonneg (a := g.edist p x)
    linarith
  have hwhole : g.IsGeodesicOn η (Icc (-1 / 3 : ℝ) 1) := by
    intro t ht
    exact hγ.comp_affine (3 / 4) (1 / 4) t
      ⟨by dsimp; linarith [ht.1], by dsimp; linarith [ht.2]⟩
  have hrad : g.IsGeodesicOn (fun t : ℝ => e (t • v)) (Icc (-1 / 3 : ℝ) 1) := by
    intro t ht
    apply hgeo v hv t
    change t • v ∈ Metric.ball 0 R
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    exact (mul_le_mul_of_nonneg_right ht' (norm_nonneg v)).trans_lt
      (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hv)
  have hradw : HasDerivAt (fun t : ℝ => extChartAt (𝓡 n) q (e (t • v))) w 0 := by
    have hdline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hcomp := hed.comp_hasDerivAt_of_eq 0 hdline (by simp)
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, hLv] using hcomp
  have heq := hrad.eq_nhds_on_of_initial_data hwhole (convex_Icc _ _).isPreconnected
    (t₀ := 0) (by norm_num) q
    (by simpa only [zero_smul, he0] using mem_extChartAt_source q)
    (by simpa only [zero_smul, he0] using hη0.symm)
    (hradw.deriv.trans hw.deriv.symm)
  refine ⟨v, hv, hvnorm, ?_, ?_, heq⟩
  · simpa only [one_smul, hη1] using (heq 1 (by norm_num)).self_of_nhds
  · have hpq : g.edist p q = ENNReal.ofReal (1 / 4) * g.edist p x := by
      have h := hmin 0 (by norm_num) (1 / 4) (by norm_num)
      simpa only [hγ0, zero_sub, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using h
    rw [hpq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4), hvnorm]
    ring

end PoincareConjecture.RiemannianMetric
