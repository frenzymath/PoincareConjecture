import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Reparametrization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EquationBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.GaussDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.SmoothReplacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.WeakMap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Pullback













noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

open HarmonicCoordinates

variable {n : ℕ}



theorem exists_uniform_harmonic_radius (hn : 2 ≤ n)
    {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K) :
    ∃ r C H : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < H ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) →
        (∀ x w, g.euclideanCoefficients x x w = inner ℝ x w) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        ∃ F : UniformHarmonicLift g 0 r C H,
          MapsTo F.e (Metric.ball 0 (2 * r)) (Metric.ball 0 R) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨δ, hδ, hregularity⟩ := exists_uniform_harmonic_metric_halfHolder hn
  obtain ⟨s, ρ, hs, hsquarter, hsR, hρ, hρs, hweak⟩ :=
    exists_uniform_weakHarmonicCoordinate_inverse_metric_close hn hR hK hδ
  let S := ρ / 8
  have hS : 0 < S := by dsimp [S]; positivity
  have hS1 : S ≤ 1 := by dsimp [S]; linarith
  obtain ⟨H, hH, hregularity⟩ := hregularity S (1 / 9) 9 K hS hS1
    (by norm_num) (by norm_num) (by norm_num) hK
  let r := S / 256
  have hr : 0 < r := by dsimp [r]; positivity
  have hrS : 2 * r = S / 128 := by dsimp [r]; ring
  have hρR : ρ < R := by linarith
  refine ⟨r, 9, H, hr, by norm_num, hH, fun g D hell hgauss hcurv => ?_⟩
  obtain ⟨w, hw, hmap⟩ := hweak g D hell hgauss hcurv
  have hrep (i : Fin n) := exists_smooth_weakHarmonicReplacement_of_smooth D
    (by positivity : 0 < 2 * s) (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    (w i) (hw i)
  choose U hUs hU hharmU using hrep
  obtain ⟨F, hFeq, hsource, htarget, hF, hFi, hF0, hFi0, hclose, hharmF, hnear⟩ :=
    hmap U hUs hU
  have hsourceR : F.source ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [hsource]
    exact Metric.ball_subset_ball hρR.le
  have hbound : ∀ x ∈ F.source, ∀ v : EuclideanSpace ℝ (Fin n),
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.inner x v v ∧
        g.inner x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 :=
    fun x hx v => hell x (hsourceR hx) v
  have hpull : ∀ x ∈ Metric.ball 0 (ρ / 4), ∀ v : EuclideanSpace ℝ (Fin n),
      (1 / 9 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients F.symm x v v ∧
        g.pullbackCoefficients F.symm x v v ≤ 9 * ‖v‖ ^ 2 := by
    intro x hx v
    have h := g.inverse_pullback_elliptic F hF hclose
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 9 / 4)
      hbound (htarget hx) v
    norm_num at h ⊢
    exact h
  have hB : ContDiffOn ℝ ∞ (g.pullbackCoefficients F.symm) (Metric.ball 0 (ρ / 4)) := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      (hFi.contDiffAt (F.open_target.mem_nhds (htarget hx))).contMDiffAt).contDiffWithinAt
  obtain ⟨h, hmetric, hellglobal⟩ := exists_extension_on_ball hS
    (by dsimp [S]; linarith : S < ρ / 4)
    (by norm_num : (0 : ℝ) < 1 / 9) (by norm_num : (1 / 9 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 9) (g.pullbackCoefficients F.symm) hB
    (fun x _ v z => g.symm _ _ _) hpull
  let D' := h.euclideanLeviCivitaData
  have hStarget : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S ⊆ F.target :=
    (Metric.ball_subset_ball (by dsimp [S]; linarith : S ≤ ρ / 4)).trans htarget
  have hsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm (Metric.ball 0 S) :=
    contMDiffOn_iff_contDiffOn.mpr (hFi.mono hStarget)
  have hinv (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S) :
      (mfderiv (𝓡 n) (𝓡 n) F.symm x).IsInvertible := by
    apply g.isInvertible_mfderiv_of_positive_pullback
    intro v hv
    rw [← hmetric x hx]
    exact h.pos x v hv
  have hharm (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S) (i : Fin n) :
      D'.laplacian (fun y : EuclideanSpace ℝ (Fin n) => y i) x = 0 :=
    D.harmonic_coordinates_of_inverse_pullback D' F hF hFi Metric.isOpen_ball
      hStarget hmetric hharmF hx i
  have hcurv' (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S) :
      D'.curvatureTensorNorm x ≤ K := by
    have heq : D'.curvatureTensorNorm x = D.curvatureTensorNorm (F.symm x) := by
      apply D'.curvatureTensorNorm_eq_pullback_euclidean D
        (hsmooth.contMDiffAt (Metric.isOpen_ball.mem_nhds hx))
      · filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
        exact hinv y hy
      · filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
        intro v z
        exact congrArg (fun B => B v z) (hmetric y hy)
    rw [heq]
    exact hcurv _ (hsourceR (F.map_target (hStarget hx)))
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have hnear' (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S) :
      ‖h.euclideanCoefficients x - B₀‖ < δ := by
    rw [hmetric x hx]
    exact hnear x (hStarget hx)
  obtain ⟨hderiv, hholder⟩ := hregularity h D' (fun x _ v => hellglobal x v) hcurv' hharm hnear'
  have hsmallS : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball (by rw [hrS]; linarith)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm (Metric.ball 0 (2 * r)) :=
    hsmooth.mono hsmallS
  have hupper (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * r))
      (v : EuclideanSpace ℝ (Fin n)) : g.pullbackCoefficients F.symm x v v ≤ 9 * ‖v‖ ^ 2 := by
    rw [← hmetric x (hsmallS hx)]
    exact (hellglobal x v).2
  refine ⟨{
    e := F.symm
    h := h
    D' := D'
    he := he
    he0 := hFi0
    hlocal := fun x hx => hinv x (hsmallS hx)
    hpullback := fun x hx => hmetric x (hsmallS hx)
    helliptic := fun x _ v => by simpa only [one_div] using hellglobal x v
    hderiv := fun x hx => hderiv x (by simpa only [hrS] using hx)
    hholder := fun x y hx hy => hholder x (by simpa only [hrS] using hx)
      y (by simpa only [hrS] using hy)
    hharmonic := fun x hx i => hharm x (hsmallS hx) i
    hdist := fun x hx => g.edist_center_le_of_pullback_upper (by positivity : 0 < 2 * r)
      he hFi0 (by norm_num : (0 : ℝ) ≤ 9) hupper hx
  }, ?_⟩
  intro x hx
  exact hsourceR (F.map_target (hStarget (hsmallS hx)))

end PoincareConjecture.RiemannianMetric
