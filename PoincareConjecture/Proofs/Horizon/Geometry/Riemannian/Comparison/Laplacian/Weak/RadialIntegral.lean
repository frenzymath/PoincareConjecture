import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Integral.RadialComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.RayInterval
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.CutoffComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Nonterminal










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.VolumeComparison



theorem integral_ray_indicator
    {E : Type*} {S : Set E} {θ : E} [SMul ℝ E] {c r : ℝ}
    (hcut : ∀ t : ℝ, 0 < t → (t • θ ∈ S ↔ t < c)) (F : ℝ → ℝ) :
    (∫ t in Ioo (0 : ℝ) r, ((fun t : ℝ => t • θ) ⁻¹' S).indicator F t) =
      ∫ t in Ioo (0 : ℝ) (min c r), F t := by
  classical
  calc
    _ = ∫ t in Ioo (0 : ℝ) r, (Iio c).indicator F t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [indicator, mem_preimage, hcut t ht.1, mem_Iio]
    _ = ∫ t in Iio c ∩ Ioo (0 : ℝ) r, F t := by
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    _ = _ := by
      have hset : Iio c ∩ Ioo (0 : ℝ) r = Ioo 0 (min c r) := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioo, lt_min_iff]
        tauto
      rw [hset]

end Poincare.VolumeComparison

namespace PoincareConjecture.RiemannianMetric

open Poincare.VolumeComparison Poincare.Analysis.RadialIntegration

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]



theorem radial_integral_laplacian_comparison
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {p : M} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    {L : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))}
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 (m + 1)) p).symm
      (extChartAt (𝓡 (m + 1)) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 (m + 1)) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 (m + 1)) x, 0 ≤ D.ricci x v v)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hpos : ∀ t ∈ Icc (0 : ℝ) r, 0 ≤ f t) :
    let S := localMinimizingSet (fun v => g.edist p (e v)) R
    let H := fun t : ℝ => (S \ terminalRadialPoints S R).indicator
      (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin (m + 1))));
    -(∫ t in Ioo (0 : ℝ) r, (t ^ m * H t) * deriv f t) ≤
      ∫ t in Ioo (0 : ℝ) r, (m : ℝ) / t * f t * (t ^ m * H t) := by
  classical
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  let H := fun t : ℝ => g.pullbackVolumeDensity e
    (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))
  have hR : 0 < R := hr.trans hrR
  have hθ : ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp θ.property
  have hball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) r) :
      t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ Metric.ball 0 R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1, hθ, mul_one]
    exact ht.2.trans_lt hrR
  have h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ S := by
    refine ⟨by simpa using hR, ?_⟩
    change g.edist p (e 0) = ENNReal.ofReal ‖(0 : EuclideanSpace ℝ (Fin (m + 1)))‖
    simp only [he0, edist, Manifold.riemannianEDist_self, norm_zero, ENNReal.ofReal_zero]
  have hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S := by
    intro v hv a ha0 ha1
    exact radial_minimizing_star g he hv
      (fun t ht => ((hgeo v hv.1).2 t ht).1)
      (fun t ht => ((hgeo v hv.1).2 t ht).2) a ha0 ha1
  obtain ⟨c, hc0, hcR, hcut⟩ := exists_ray_interval_sdiff_terminal h0
    (fun _ hv => hv.1) hstar hθ
  let d := min c r
  have hd0 : 0 ≤ d := le_min hc0 hr.le
  have hdr : d ≤ r := min_le_right _ _
  have hrestrict (F : ℝ → ℝ) :
      (∫ t in Ioo (0 : ℝ) r, if t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T
        then F t else 0) = ∫ t in Ioo (0 : ℝ) d, F t :=
    by simpa only [indicator, mem_preimage] using integral_ray_indicator hcut F
  have hleft : (fun t : ℝ => (t ^ m * (S \ T).indicator
      (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))) * deriv f t) =
      fun t => if t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T
        then (t ^ m * H t) * deriv f t else 0 := by
    funext t
    by_cases ht : t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T <;>
      simp [indicator, ht, H]
  have hright : (fun t : ℝ => (m : ℝ) / t * f t * (t ^ m * (S \ T).indicator
      (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin (m + 1)))))) =
      fun t => if t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T
        then (m : ℝ) / t * f t * (t ^ m * H t) else 0 := by
    funext t
    by_cases ht : t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T <;>
      simp [indicator, ht, H]
  dsimp only
  rw [hleft, hright, hrestrict, hrestrict]
  rcases hd0.eq_or_lt with hd | hd
  · simp only [← hd, Ioo_self, Measure.restrict_empty, integral_zero_measure, neg_zero, le_refl]
  have hHcont : ContinuousOn H (Icc (0 : ℝ) d) := by
    intro t ht
    exact ((g.continuousAt_pullbackVolumeDensity_of_contMDiffAt
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hball t ⟨ht.1, ht.2.trans hdr⟩)))).comp
      (f := fun s : ℝ => s • (θ : EuclideanSpace ℝ (Fin (m + 1))))
      (show ContinuousAt (fun s : ℝ => s • (θ : EuclideanSpace ℝ (Fin (m + 1)))) t
        from continuousAt_id.smul continuousAt_const)).continuousWithinAt
  have hHdiff (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) d) : DifferentiableAt ℝ H t := by
    have htS := (hcut t ht.1).mpr (ht.2.trans_le (min_le_left _ _))
    have hi := g.isInvertible_mfderiv_on_nonterminal D he he0 hed
      (fun v hv => (hgeo v hv).1) (fun v hv t ht => ((hgeo v hv).2 t ht).1) _ htS
    have hρ := (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hball t ⟨ht.1.le, ht.2.le.trans hdr⟩)))
      hi.injective).1
    exact (hρ.comp t (show ContDiffAt ℝ ∞
      (fun s : ℝ => s • (θ : EuclideanSpace ℝ (Fin (m + 1)))) t by fun_prop)).differentiableAt
      (by simp)
  have hanti : AntitoneOn H (Ioo (0 : ℝ) d) := by
    have h := g.antitoneOn_radialDensity_div_modelS D (by omega) hR (κ := 0)
      (by norm_num) hL he he0 hed hgeo (by simpa using hRic) θ
    intro t ht s hs hts
    have htS := (hcut t ht.1).mpr (ht.2.trans_le (min_le_left _ _))
    have hsS := (hcut s hs.1).mpr (hs.2.trans_le (min_le_left _ _))
    change t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T at htS
    change s • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T at hsS
    have h' := h ⟨ht.1, ht.2.trans_le hdr |>.trans hrR⟩
      ⟨hs.1, hs.2.trans_le hdr |>.trans hrR⟩ hts
    change s ^ m * (S \ T).indicator (g.pullbackVolumeDensity e) (s • (θ : EuclideanSpace ℝ (Fin (m + 1)))) /
        modelS 0 s ^ m ≤ t ^ m * (S \ T).indicator (g.pullbackVolumeDensity e)
          (t • (θ : EuclideanSpace ℝ (Fin (m + 1)))) / modelS 0 t ^ m at h'
    simpa only [H, modelS_zero_curvature, indicator_of_mem htS,
      indicator_of_mem hsS, mul_div_cancel_left₀ _ (pow_ne_zero _ ht.1.ne'),
      mul_div_cancel_left₀ _ (pow_ne_zero _ hs.1.ne')] using h'
  exact (radial_integral_comparison_of_antitone hd hm hf
    (fun t ht => hpos t ⟨ht.1, ht.2.trans hdr⟩) hHcont hHdiff
    (fun _ _ => Real.sqrt_nonneg _) hanti).2.2

end PoincareConjecture.RiemannianMetric
