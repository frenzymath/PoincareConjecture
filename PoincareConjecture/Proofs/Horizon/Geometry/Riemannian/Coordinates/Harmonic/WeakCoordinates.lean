import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakReplacement
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n]
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem existsUnique_weakHarmonicReplacement_of_smooth (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hq : ContDiff ℝ ∞ q) :
    ∃! w : H1Zero D (Metric.ball 0 R),
      ∀ f : EnergyTest D (Metric.ball 0 R),
        (∫ x, (q x + (toL2 D (Metric.ball 0 R) w) x) *
          D.laplacian f x ∂g.volumeMeasure) = 0 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨R, 2 * R, hR, by linarith⟩
  let Q := fun x => b x * q x
  have hQc : HasCompactSupport Q := b.hasCompactSupport.mul_right
  have hQs : ContDiff ℝ ∞ Q := b.contDiff.mul hq
  have hQeq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 R) : Q x = q x := by
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [Q, hb]
  have hint (w : H1Zero D (Metric.ball 0 R)) (f : EnergyTest D (Metric.ball 0 R)) :
      (∫ x, (q x + (toL2 D (Metric.ball 0 R) w) x) * D.laplacian f x ∂g.volumeMeasure) =
        ∫ x, (Q x + (toL2 D (Metric.ball 0 R) w) x) * D.laplacian f x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Metric.ball 0 R
    · rw [hQeq x hx]
    · have hz := D.laplacian_eq_zero_of_notMem_tsupport
        (f := (f : EuclideanSpace ℝ (Fin n) → ℝ)) (fun ht => hx (f.support_subset ht))
      simp [hz]
  obtain ⟨w, hw, huniq⟩ := existsUnique_weakHarmonicReplacement_on_ball D hR hQs hQc
  refine ⟨w, fun f => (hint w f).trans (hw f), ?_⟩
  intro w' hw'
  exact huniq w' (fun f => (hint w' f).symm.trans (hw' f))

theorem existsUnique_weakHarmonicCoordinate (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) (i : Fin n) :
    ∃! w : H1Zero D (Metric.ball 0 R),
      ∀ f : EnergyTest D (Metric.ball 0 R),
        (∫ x, (x i + (toL2 D (Metric.ball 0 R) w) x) *
          D.laplacian f x ∂g.volumeMeasure) = 0 := by
  apply existsUnique_weakHarmonicReplacement_of_smooth D hR
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

end PoincareConjecture.HarmonicCoordinates
