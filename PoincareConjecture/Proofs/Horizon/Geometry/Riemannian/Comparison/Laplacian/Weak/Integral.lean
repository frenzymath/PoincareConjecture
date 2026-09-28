import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Weak.RadialTest
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Weak.RadialGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.AlmostEverywhere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

open Poincare.VolumeComparison

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] {g : RiemannianMetric (m + 1) M}

theorem integral_distance_mul_laplacian_le (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g) (hRic : D.NonnegativeRicciCurvature)
    (p : M) (A : ℝ) (hA : 0 < A) (φ : M → ℝ)
    (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hAdist : ∀ x ∈ tsupport φ, A ≤ (g.edist p x).toReal) :
    (∫ x, (g.edist p x).toReal * D.laplacian φ x ∂g.volumeMeasure) ≤
      (m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure := by
  classical
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (g.continuous_toReal_edist p).continuousOn
  let r := max C 0 + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right C 0]
  have hsupport : tsupport φ ⊆ g.ball p r := by
    intro x hx
    have hxC : (g.edist p x).toReal ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hC x hx
    change g.edist p x < ENNReal.ofReal r
    apply (ENNReal.toReal_lt_toReal (g.edist_ne_top p x) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hr.le]
    dsimp [r]
    linarith [le_max_left C 0]
  let R := r + 1
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  have hcompact := g.isCompact_closure_ball_of_metricComplete hcomplete p R
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hcut, hinj, _⟩ :=
    exists_precompact_polar_volume g p (by omega) hR hcompact
  have hcover := image_localMinimizingSet_eq_ball g p hR hcompact L e hL he0 hed
    (fun v hv => (hgeo v hv).1)
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  let F := fun x => mvfderiv (𝓡 (m + 1)) (fun y => (g.edist p y).toReal) x (D.gradient φ x)
  let P := fun (f : M → ℝ)
      (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : ℝ) =>
    t ^ m * (S \ T).indicator (fun v => f (e v) * g.pullbackVolumeDensity e v)
      (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))
  let Q := fun (f : M → ℝ) θ => ∫ t in Ioo (0 : ℝ) r, P f θ t
  let H := fun (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) (t : ℝ) =>
    (S \ T).indicator (g.pullbackVolumeDensity e)
      (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))
  have hP (f : M → ℝ) (θ) (t) :
      P f θ t = (t ^ m * H θ t) * f (e (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))) := by
    dsimp [P, H]
    rw [indicator_mul_right]
    ring
  have hH (θ) (t) : 0 ≤ H θ t := by
    exact indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) _
  obtain ⟨hFint, hgreen⟩ := D.integral_distance_mul_laplacian p hφ hc
  have hφint : Integrable φ g.volumeMeasure := hφ.continuous.integrable_of_hasCompactSupport hc
  have hFzero : ∀ x ∉ g.ball p r, F x = 0 := by
    intro x hx
    have hnot : x ∉ tsupport φ := fun hs => hx (hsupport hs)
    simp only [F, D.gradient_eq_zero_of_notMem_tsupport hnot, map_zero]
  have hφzero : ∀ x ∉ g.ball p r, φ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hs => hx (hsupport hs))
  have hpolar (f : M → ℝ) (hi : Integrable f g.volumeMeasure)
      (hz : ∀ x ∉ g.ball p r, f x = 0) :
      (∫ x, f x ∂g.volumeMeasure) = ∫ θ, Q f θ ∂volume.toSphere := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    simpa only [Q, P, S, T, Nat.add_sub_cancel] using
      integral_ball_eq_polar_of_injOn g p (by omega) hr hrR.le he hcover hcut hinj hi.integrableOn
  have hQint (f : M → ℝ) (hi : Integrable f g.volumeMeasure) :
      Integrable (Q f) volume.toSphere := by
    simpa only [Q, P, S, T, Nat.add_sub_cancel] using
      integrable_polar_integral_ball_of_injOn g p hr hrR.le he hcover hcut hinj hi.integrableOn
  have hae := ae_ae_polar_of_ae_ball_of_injOn g p hr hrR.le he hcover hcut hinj
    (ae_restrict_of_ae (g.ae_mDifferentiableAt_distance p))
  have hray : ∀ᵐ θ ∂volume.toSphere, Q F θ =
      ∫ t in Ioo (0 : ℝ) r, (t ^ m * H θ t) *
        deriv (fun s => φ (e (s • (θ : EuclideanSpace ℝ (Fin (m + 1)))))) t := by
    filter_upwards [hae] with θ hθ
    apply integral_congr_ae
    filter_upwards [hθ, ae_restrict_mem measurableSet_Ioo] with t ht htr
    rw [hP]
    by_cases hh : H θ t = 0
    · simp [hh]
    · have htS : t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T := by
        by_contra hnot
        exact hh (indicator_of_notMem hnot _)
      congr 1
      exact g.mvfderiv_distance_gradient_eq_radial_deriv D he
        (fun v hv s hs => ((hgeo v hv).2 s hs).1)
        (fun v hv s hs => ((hgeo v hv).2 s hs).2)
        (mem_sphere_zero_iff_norm.mp θ.property) htr.1 htS (ht hh)
        ((hφ _).mdifferentiableAt (by simp))
  have hright_bound (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) r) :
      (m : ℝ) / t * φ (e (t • θ.val)) *
          (t ^ m * H θ t) ≤ (m : ℝ) / A * P φ θ t := by
    rw [hP]
    by_cases hh : H θ t = 0
    · simp [hh]
    by_cases hz : φ (e (t • θ.val)) = 0
    · simp [hz]
    have htS : t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T := by
      by_contra hnot
      exact hh (indicator_of_notMem hnot _)
    have hd : (g.edist p (e (t • θ.val))).toReal = t := by
      have hdist : g.edist p (e (t • θ.val)) = ENNReal.ofReal ‖t • θ.val‖ := htS.1.2
      rw [hdist, ENNReal.toReal_ofReal (norm_nonneg _), norm_smul,
        mem_sphere_zero_iff_norm.mp θ.property, mul_one, Real.norm_of_nonneg ht.1.le]
    have hAt : A ≤ t := by
      rw [← hd]
      exact hAdist _ (subset_tsupport _ hz)
    have hfrac : (m : ℝ) / t ≤ (m : ℝ) / A :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hA hAt
    have hmul := mul_le_mul_of_nonneg_right hfrac
      (mul_nonneg (hφ0 (e (t • θ.val))) (mul_nonneg (pow_nonneg ht.1.le m) (hH θ t)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hinnerint : ∀ᵐ θ ∂volume.toSphere, IntegrableOn (P φ θ) (Ioo (0 : ℝ) r) := by
    simpa only [P, S, T, Nat.add_sub_cancel] using
      ae_integrable_polar_ball_of_injOn g p hr hrR.le he hcover hcut hinj hφint.integrableOn
  have hineq : ∀ᵐ θ ∂volume.toSphere, -Q F θ ≤ (m : ℝ) / A * Q φ θ := by
    filter_upwards [hray, hinnerint] with θ hθ hiθ
    have hrad := g.radial_integral_laplacian_comparison_test D hm hr hrR hL he he0 hed hgeo
      (fun x _ v => hRic x v) θ hφ hφ0
    rw [hθ]
    apply hrad.trans
    calc
      _ ≤ ∫ t in Ioo (0 : ℝ) r, (m : ℝ) / A * P φ θ t := by
        apply integral_mono_of_nonneg ?_ (hiθ.const_mul _) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) ht.1.le) (hφ0 _))
            (mul_nonneg (pow_nonneg ht.1.le _) (hH θ t))
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact hright_bound θ t ht
      _ = (m : ℝ) / A * Q φ θ := integral_const_mul _ _
  rw [hgreen]
  change -(∫ x, F x ∂g.volumeMeasure) ≤ (m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure
  rw [hpolar F hFint hFzero, hpolar φ hφint hφzero, ← integral_neg, ← integral_const_mul]
  exact integral_mono_ae (hQint F hFint).neg ((hQint φ hφint).const_mul _) hineq

end PoincareConjecture.LeviCivitaData
