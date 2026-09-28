import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Hessian.UniformSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Hessian.Transform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.UpperSupport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in

theorem exists_uniform_concave_transformed_busemann
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    (q : M)
    (hpos : ∀ u v, g.inner q u u = 1 → g.inner q v v = 1 →
      g.inner q u v = 0 → 0 < D.sectionalCurvature q u v)
    (p : M) :
    ∃ r > 0, ∃ δ > 0, ∀ {ray : ℝ → M}, IsRay ray → ray 0 = p →
      ∀ {curve : ℝ → M} {a b : ℝ}, g.IsGeodesicOn curve (Icc a b) →
        (∀ t ∈ Icc a b, (g.edist (curve t) q).toReal ≤ r) →
        (∀ t ∈ Icc a b, g.inner (curve t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1) = 1) →
        ConcaveOn ℝ (Icc a b)
          (fun t => 1 - Real.exp (-busemann ray (curve t)) + δ * t ^ 2) := by
  obtain ⟨η, hη, hη1, L, _, r, hr, hsupport⟩ :=
    g.exists_uniform_transverse_distance_upper_support_on_edist_ball
      D hcomplete hsec q hpos
  let B := dist p q + r
  let δ := Real.exp (-B) * η / 2
  have hδ : 0 < δ := div_pos (mul_pos (Real.exp_pos _) hη) (by norm_num)
  refine ⟨r, hr, δ, hδ, ?_⟩
  intro ray hray hray0 curve a b hcurve hball hspeed
  have hcontinuous : ContinuousOn curve (Icc a b) := fun t ht =>
    (hcurve.contMDiffAt ht).continuousAt.continuousWithinAt
  have happrox (T : ℝ) (hT : 0 ≤ T) (hlarge : L + dist p q ≤ T) :
      ConcaveOn ℝ (Icc a b)
        (fun t => 1 - Real.exp (-busemannApprox ray T (curve t)) + δ * t ^ 2) := by
    have hTp : dist (ray T) p = T := by
      rw [← hray0, hray hT le_rfl, sub_zero, abs_of_nonneg hT]
    have hfar : L ≤ (g.edist (ray T) q).toReal := by
      have hh := dist_triangle (ray T) q p
      rw [hTp, dist_comm q p] at hh
      rw [← hdist]
      linarith
    have hc : ContinuousOn (fun t => 1 - Real.exp (-busemannApprox ray T (curve t)))
        (Icc a b) := by
      have hd : ContinuousOn (fun t => dist (ray T) (curve t) - T) (Icc a b) :=
        ((continuous_const.dist continuous_id).comp_continuousOn hcontinuous).sub continuousOn_const
      exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn hd.neg)
    have hh : ConcaveOn ℝ (Icc a b)
        (fun t => (1 - Real.exp (-busemannApprox ray T (curve t))) - (-δ) * t ^ 2) := by
      apply Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support hc
      intro t ht ε hε
      have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
      obtain ⟨U, f, hU, htU, hf, htouch, hmajor, _, hhess⟩ :=
        hsupport (curve t) (hball t htcc) (ray T) hfar
      let f₀ : M → ℝ := fun y => -T + f y
      let F : M → ℝ := fun y => 1 - Real.exp (-f₀ y)
      have hft : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (curve t) :=
        hf.contMDiffAt (hU.mem_nhds htU)
      have hf₀ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f₀ U := contMDiffOn_const.add hf
      have hf₀t : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f₀ (curve t) :=
        hf₀.contMDiffAt (hU.mem_nhds htU)
      have hF : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F U := by
        intro y hy
        exact (contMDiffAt_const.sub
          ((Real.contDiff_exp.contMDiff.contMDiffAt).comp y
            ((hf₀.contMDiffAt (hU.mem_nhds hy)).neg))).contMDiffWithinAt
      have hu : ContDiffAt ℝ 2 (F ∘ curve) t :=
        (((hF.contMDiffAt (hU.mem_nhds htU)).comp t
          (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hcurve htcc)).contDiffAt).of_le
            (by decide)
      refine ⟨F ∘ curve, hu, ?_, ?_, ?_⟩
      · change 1 - Real.exp (-(-T + f (curve t))) =
          1 - Real.exp (-busemannApprox ray T (curve t))
        rw [htouch, ← hdist]
        simp only [busemannApprox, sub_eq_add_neg, add_comm]
      · have hnear : ∀ᶠ s in 𝓝 t, curve s ∈ U :=
          (hcurve.contMDiffAt htcc).continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
        filter_upwards [hnear] with s hs
        have hvalue : busemannApprox ray T (curve s) ≤ f₀ (curve s) := by
          have hm := hmajor (curve s) hs
          rw [← hdist] at hm
          dsimp [busemannApprox, f₀]
          linarith
        exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hvalue)) 1
      · rw [(D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU hF hcurve htcc htU).deriv]
        let w := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1
        have hdf : mvfderiv (𝓡 n) f₀ (curve t) = mvfderiv (𝓡 n) f (curve t) := by
          dsimp only [f₀]
          rw [mvfderiv_fun_add mdifferentiableAt_const (hft.mdifferentiableAt (by simp)),
            mvfderiv_const, zero_add]
        have hfbound : D.hessian f₀ (curve t) w w ≤
            -η * (g.inner (curve t) w w - (mvfderiv (𝓡 n) f₀ (curve t) w) ^ 2) := by
          rw [D.hessian_const_add_at hft, hdf]
          exact hhess w
        have hbound := D.hessian_one_sub_exp_neg_le_of_transverse_bound hf₀t w hη1 hfbound
        have hw : g.inner (curve t) w w = 1 := hspeed t htcc
        rw [hw, mul_one] at hbound
        have hvalue : f₀ (curve t) ≤ B := by
          have htri := dist_triangle (ray T) p (curve t)
          rw [hTp] at htri
          have htri' := dist_triangle p q (curve t)
          have hclose : dist q (curve t) ≤ r := by
            rw [dist_comm, hdist]
            exact hball t htcc
          dsimp only [f₀, B]
          rw [htouch, ← hdist]
          linarith
        have he := Real.exp_le_exp.mpr (neg_le_neg hvalue)
        have hnegative := mul_le_mul_of_nonneg_right (neg_le_neg he) hη.le
        have hgap : -Real.exp (-B) * η = 2 * (-δ) := by dsimp only [δ]; ring
        apply hbound.trans
        exact hnegative.trans (by rw [hgap]; linarith)
    simpa only [neg_mul, sub_neg_eq_add] using hh
  have hlimit (s : ℝ) : Tendsto
      (fun T => 1 - Real.exp (-busemannApprox ray T (curve s)) + δ * s ^ 2) atTop
      (𝓝 (1 - Real.exp (-busemann ray (curve s)) + δ * s ^ 2)) :=
    (tendsto_const_nhds.sub ((Real.continuous_exp.tendsto _).comp
      (tendsto_busemannApprox hray (curve s)).neg)).add_const _
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto ((hlimit x).const_mul α |>.add ((hlimit y).const_mul β))
    (hlimit (α * x + β * y))
  filter_upwards [eventually_ge_atTop (max 0 (L + dist p q))] with T hT
  have hh := (happrox T ((le_max_left _ _).trans hT) ((le_max_right _ _).trans hT)).2
    hx hy hα hβ hsum
  simpa only [smul_eq_mul] using hh

end PoincareConjecture.RiemannianMetric
