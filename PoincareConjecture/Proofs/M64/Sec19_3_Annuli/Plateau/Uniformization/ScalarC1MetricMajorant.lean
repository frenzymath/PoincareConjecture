import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarC1Pullback
import Mathlib.Geometry.Manifold.SmoothApprox

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Form" => Plane →L[ℝ] Plane →L[ℝ] ℝ

set_option maxHeartbeats 800000 in

theorem scalarContinuousForm_exists_smooth_metric_majorant
    (A : Plane → Form) (hA : Continuous A) (hnonneg : ∀ x v, 0 ≤ A x v v)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ q : RiemannianMetric 2 Plane, ∀ x v : Plane,
      A x v v + delta * ‖v‖ ^ 2 ≤ q.inner x v v ∧
      q.inner x v v ≤ A x v v + 2 * delta * ‖v‖ ^ 2 := by
  let : NormedAddCommGroup Form := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ Form := ContinuousLinearMap.toNormedSpace
  obtain ⟨B, hBs, hBclose, -⟩ := Continuous.exists_contDiff_approx
    (E := Plane) (F := Form) (f := A) (ε := fun _ => delta / 2)
    (⊤ : ℕ∞) hA continuous_const (fun _ => half_pos hdelta)
  let R : Form := innerSL ℝ
  let C : Plane → Form := fun x =>
    (1 / 2 : ℝ) • (B x + (B x).flip) + ((3 / 2 : ℝ) * delta) • R
  have hflipLinear : ContDiff ℝ ∞ (fun B : Form => B.flip) := by
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Form) (F := Form)
      (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearMap
  have hflip : ContDiff ℝ ∞ (fun x => (B x).flip) := hflipLinear.comp hBs
  have hCs : ContDiff ℝ ∞ C := by
    exact ((contDiff_const (c := (1 / 2 : ℝ))).smul (hBs.add hflip)).add
      (contDiff_const (c := ((3 / 2 : ℝ) * delta) • R))
  have hCvalue (x v w : Plane) : C x v w =
      (B x v w + B x w v) / 2 + (3 / 2 : ℝ) * delta * inner ℝ v w := by
    change (1 / 2 : ℝ) * (B x v w + B x w v) +
      ((3 / 2 : ℝ) * delta) * inner ℝ v w = _
    ring
  have hCdiag (x v : Plane) : C x v v = B x v v + (3 / 2 : ℝ) * delta * ‖v‖ ^ 2 := by
    rw [hCvalue, real_inner_self_eq_norm_sq]
    ring
  have hbounds (x v : Plane) :
      A x v v + delta * ‖v‖ ^ 2 ≤ C x v v ∧
      C x v v ≤ A x v v + 2 * delta * ‖v‖ ^ 2 := by
    have herr := (B x - A x).le_opNorm₂ v v
    simp only [sub_apply, Real.norm_eq_abs] at herr
    have hclose : ‖B x - A x‖ ≤ delta / 2 := by
      simpa only [dist_eq_norm] using (hBclose x).le
    have hmul := mul_le_mul_of_nonneg_right hclose (sq_nonneg ‖v‖)
    have habs : |B x v v - A x v v| ≤ (delta / 2) * ‖v‖ ^ 2 := by
      nlinarith
    rw [hCdiag]
    constructor <;> nlinarith [(abs_le.mp habs).1, (abs_le.mp habs).2]
  have hsymm (x v w : Plane) : C x v w = C x w v := by
    rw [hCvalue, hCvalue, real_inner_comm w v]
    ring
  have hpos (x v : Plane) (hv : v ≠ 0) : 0 < C x v v := by
    exact (add_pos_of_nonneg_of_pos (hnonneg x v)
      (mul_pos hdelta (sq_pos_of_pos (norm_pos_iff.mpr hv)))).trans_le (hbounds x v).1
  exact ⟨RiemannianMetric.ofEuclideanCoefficients C hCs hsymm hpos, hbounds⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarC1_exists_smooth_metric_majorant
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ q : RiemannianMetric 2 Plane, ∀ x v : Plane,
      g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v) +
          delta * ‖v‖ ^ 2 ≤ q.inner x v v ∧
      q.inner x v v ≤
        g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v) +
          2 * delta * ‖v‖ ^ 2 := by
  apply scalarContinuousForm_exists_smooth_metric_majorant
    (show Plane → Form from fun x => M60.metricPullbackForm (n := 2) g f x)
    (scalarC1_pullback_continuous g f hf) _ delta hdelta
  intro x v
  change 0 ≤ g.inner (f x) (mfderiv (𝓡 2) (𝓡 n) f x v) (mfderiv (𝓡 2) (𝓡 n) f x v)
  by_cases hv : mfderiv (𝓡 2) (𝓡 n) f x v = 0
  · simp [hv]
  · exact (g.pos _ _ hv).le

end PoincareConjecture.M64Uniformization
