import PoincareConjecture.Proofs.M35.Thm12_28.MetricConnectionJets
import PoincareConjecture.Proofs.M03.Existence.FrameDeTurckDerivativeNative

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)
local notation:max "G" n:max => E n →L[ℝ] E n →L[ℝ] ℝ

private theorem gram_det_ne_zero {n : ℕ} (g : RiemannianMetric n (E n))
    (x : E n) (b : Module.Basis (Fin n) ℝ (E n)) :
    (Matrix.of (fun i j => g.inner x (b i) (b j))).det ≠ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change (Matrix.gram ℝ (show Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)
    from b)).det ≠ 0
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent

private theorem inverseGramEntry_contDiffAt {n : ℕ}
    (g : RiemannianMetric n (E n)) (x : E n)
    (b : Module.Basis (Fin n) ℝ (E n)) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun A : G n => (Matrix.of (fun a c => A (b a) (b c)))⁻¹ i j)
      (g.euclideanCoefficients x) := by
  have hgram : ContDiff ℝ ∞ (fun A : G n => fun a c => A (b a) (b c)) := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    fun_prop
  have h := (DeTurckNative.contDiffAt_matrixInverseEntries_infty
    (fun a c => g.inner x (b a) (b c)) (gram_det_ne_zero g x b)).comp
      (g.euclideanCoefficients x) hgram.contDiffAt
  exact contDiffAt_pi.mp (contDiffAt_pi.mp h i) j

theorem inverseGram_contDiffAt {n : ℕ} (g : RiemannianMetric n (E n))
    (x : E n) (b : Module.Basis (Fin n) ℝ (E n)) (i j : Fin n) :
    ContDiffAt ℝ ∞
      (fun y => (Matrix.of (fun a c => g.inner y (b a) (b c)))⁻¹ i j) x :=
  (inverseGramEntry_contDiffAt g x b i j).comp x (g.contDiffAt_euclideanCoefficients x)

theorem inverseGram_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (pseq : ℕ → E n) (p : E n) (b : Module.Basis (Fin n) ℝ (E n))
    (i j : Fin n) (r : ℕ)
    (hjet : ∀ m ≤ r, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => (Matrix.of (fun a c => (gseq k).inner y (b a) (b c)))⁻¹ i j) (pseq k))
      atTop (𝓝 (iteratedFDeriv ℝ r
        (fun y => (Matrix.of (fun a c => g.inner y (b a) (b c)))⁻¹ i j) p)) :=
  tendsto_iteratedFDeriv_smooth_comp_of_jets r (g.contDiffAt_euclideanCoefficients p)
    (fun k => (gseq k).contDiffAt_euclideanCoefficients (pseq k))
    (inverseGramEntry_contDiffAt g p b i j)
    (fun k => inverseGramEntry_contDiffAt (gseq k) (pseq k) b i j) hjet

end PoincareConjecture.M35
