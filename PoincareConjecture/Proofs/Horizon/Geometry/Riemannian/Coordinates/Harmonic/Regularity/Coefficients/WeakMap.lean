import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Reparametrization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.WeakCoordinateCloseness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.CoordinateMap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrameBounds










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem laplacian_sub_const_euclidean {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    D.laplacian (fun y => f y - c) x = D.laplacian f x := by
  have hd (y : EuclideanSpace ℝ (Fin n)) :
      mvfderiv (𝓡 n) (fun z => f z - c) y = mvfderiv (𝓡 n) f y := by
    ext v
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    exact congrArg (fun A => A v) (fderiv_sub_const (𝕜 := ℝ) (f := f) (x := y) c)
  simp only [LeviCivitaData.laplacian, LeviCivitaData.hessian,
    LeviCivitaData.hessianOnFields, hd]



theorem exists_uniform_weakHarmonicCoordinate_inverse_metric_close
    {n : ℕ} (hn : 2 ≤ n) {R K ε : ℝ} (hR : 0 < R) (hK : 0 ≤ K) (hε : 0 < ε) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ s ρ : ℝ, 0 < s ∧ s ≤ 1 / 4 ∧ 4 * s < R ∧ 0 < ρ ∧ ρ ≤ s / 2 ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) →
        (∀ x w, g.euclideanCoefficients x x w = inner ℝ x w) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        ∃ w : Fin n → H1Zero D (Metric.ball 0 (2 * s)),
          (∀ (i : Fin n) (φ : EnergyTest D (Metric.ball 0 (2 * s))),
            (∫ x, (x i + (toL2 D (Metric.ball 0 (2 * s)) (w i)) x) *
              D.laplacian φ x ∂g.volumeMeasure) = 0) ∧
          ∀ U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
            (∀ i, ContDiffOn ℝ ∞ (U i) (Metric.ball 0 (2 * s))) →
            (∀ i, U i =ᵐ[g.volumeMeasure.restrict (Metric.ball 0 (2 * s))]
              fun x => x i + (toL2 D (Metric.ball 0 (2 * s)) (w i)) x) →
            ∃ F : OpenPartialHomeomorph
                (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
              (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
                (fun x => coordinateMap U x - coordinateMap U 0) ∧
              F.source = Metric.ball 0 ρ ∧ Metric.ball 0 (ρ / 4) ⊆ F.target ∧
              ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
              F 0 = 0 ∧ F.symm 0 = 0 ∧
              (∀ x ∈ F.source,
                ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2) ∧
              (∀ x ∈ F.source, ∀ i : Fin n,
                D.laplacian (fun y => F y i) x = 0) ∧
              ∀ y ∈ F.target, ‖g.pullbackCoefficients F.symm y - B₀‖ < ε := by
  classical
  dsimp only
  let : NeZero n := ⟨by omega⟩
  let α : ℝ := ε / 16
  let β : ℝ := min (1 / 2) (ε / 24)
  let τ : ℝ := β / Real.sqrt n
  have hα : 0 < α := by dsimp only [α]; positivity
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβhalf : β ≤ 1 / 2 := min_le_left _ _
  have hβε : β ≤ ε / 24 := min_le_right _ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hτ : 0 < τ := div_pos hβ hnsqrt
  have hτeq : Real.sqrt n * τ = β := by
    dsimp only [τ]
    field_simp [ne_of_gt hnsqrt]
  have herror : 4 * α + 6 * β < ε := by dsimp only [α]; linarith
  obtain ⟨s, hs, hsquarter, hsR, hweak⟩ :=
    exists_uniform_weakHarmonicCoordinate_differential_close hn hR hK hτ
  obtain ⟨t, ht, htR, ht1, hsmall⟩ :=
    exists_small_radial_frame_of_gauss (n := n) hR hK hα
  rcases hsmall with ⟨hδ0, hδ1, hδα, hδquad, h2δα, hS0, hSα, hscale, hconn, hframe⟩
  let ρ : ℝ := min (s / 2) t
  have hρ : 0 < ρ := lt_min (by positivity) ht
  have hρs : ρ ≤ s / 2 := min_le_left _ _
  have hρt : ρ ≤ t := min_le_right _ _
  have hρΩ : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ Metric.ball 0 (2 * s) :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨s, ρ, hs, hsquarter, hsR, hρ, hρs, fun g D hell hgauss hcurv => ?_⟩
  choose w hw hdiff using hweak g D hell hgauss hcurv
  obtain ⟨T, -, -, -, -, -, hmetric, -⟩ := hframe g D hgauss hell hcurv
  have hmetricSmall (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 ρ)
      (v : EuclideanSpace ℝ (Fin n)) :
      |g.euclideanCoefficients x v v - ‖v‖ ^ 2| ≤ α * ‖v‖ ^ 2 := by
    exact (hmetric x (Metric.ball_subset_closedBall ((Metric.ball_subset_ball hρt) hx)) v).trans
      (mul_le_mul_of_nonneg_right hδquad (sq_nonneg ‖v‖))
  refine ⟨w, hw, fun U hUs hU => ?_⟩
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => coordinateMap U x - coordinateMap U 0
  have hf : ContDiffOn ℝ ∞ f (Metric.ball 0 ρ) :=
    (contDiffOn_coordinateMap (fun i => (hUs i).mono hρΩ)).sub contDiffOn_const
  have hf0 : f 0 = 0 := by simp only [f, sub_self]
  have hforward (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 ρ) :
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ β := by
    dsimp only [f]
    rw [fderiv_sub_const]
    calc
      _ ≤ Real.sqrt n * τ := norm_fderiv_coordinateMap_sub_id_le
        (fun i => ((hUs i).contDiffAt (Metric.isOpen_ball.mem_nhds (hρΩ hx))).differentiableAt
          (by simp)) hτ.le
        (fun i => hdiff i (U i) (hUs i) (hU i) x ((Metric.ball_subset_ball hρs) hx))
      _ = β := hτeq
  have hhalf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 ρ) :
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 :=
    (hforward x hx).trans hβhalf
  have hUh (i : Fin n) : ∀ x ∈ Metric.ball 0 (2 * s), D.laplacian (U i) x = 0 := by
    apply laplacian_eq_zero_of_smooth_distributional Metric.isOpen_ball
      (contMDiffOn_iff_contDiffOn.mpr (hUs i))
    intro φ
    have heq := integral_mul_eq_of_ae_eq_on Metric.isOpen_ball (hU i)
      ((D.tsupport_laplacian_subset φ).trans φ.support_subset)
    calc
      _ = ∫ x, (x i + (toL2 D (Metric.ball 0 (2 * s)) (w i)) x) *
          D.laplacian φ x ∂g.volumeMeasure := by simpa only [mul_comm] using heq
      _ = 0 := hw i φ
  obtain ⟨F, hFeq, hsource, hball, hFi, hFi0⟩ := exists_inverse_on_ball hρ hf hf0 hhalf
  have hF : ContDiffOn ℝ ∞ F F.source := by simpa only [hFeq, hsource] using hf
  refine ⟨F, hFeq, hsource, hball, hF, hFi, ?_, hFi0, ?_, ?_, ?_⟩
  · simpa only [hFeq] using hf0
  · simpa only [hFeq, hsource] using hhalf
  · intro x hx i
    have hxρ : x ∈ Metric.ball 0 ρ := by simpa only [hsource] using hx
    have heq : (fun y => F y i) = (fun y => U i y - U i 0) := by
      funext y
      rw [hFeq]
      simp only [f, PiLp.sub_apply, coordinateMap_apply]
    rw [heq, laplacian_sub_const_euclidean]
    exact hUh i x (hρΩ hxρ)
  · intro y hy
    have hyρ : F.symm y ∈ Metric.ball 0 ρ := by
      simpa only [hsource] using F.map_target hy
    have hclose : ‖fderiv ℝ F (F.symm y) -
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ β := by
      simpa only [hFeq] using hforward (F.symm y) hyρ
    exact (RiemannianMetric.norm_inverse_pullback_sub_innerSL_le hα.le hβ.le hβhalf
      g F hF hy (hmetricSmall (F.symm y) hyρ) hclose).trans_lt herror

end PoincareConjecture.HarmonicCoordinates
