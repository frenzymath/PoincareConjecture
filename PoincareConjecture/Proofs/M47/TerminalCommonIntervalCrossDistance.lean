import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCrossCapture
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} {X : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X]
  [T3Space M] [T3Space N] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]

theorem terminalCommonInterval_cross_distance
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : RiemannianMetric 3 X) (hg : MetricComplete g) (hk : MetricComplete k)
    (e : OpenPartialHomeomorph M X) (f : OpenPartialHomeomorph N X)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) 1 f.symm f.target)
    (p : M) (q : N) {R L lambda : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hlambda : 0 < lambda)
    (hes : {z | g.edist p z ≤ ENNReal.ofReal (4 * (R + 1))} ⊆ e.source)
    (hfs : {z | k.edist q z ≤ ENNReal.ofReal (4 * (L + 1))} ⊆ f.source)
    (heb : ∀ z, g.edist p z ≤ ENNReal.ofReal (4 * (R + 1)) →
      ∀ v : TangentSpace (𝓡 3) z,
        lambda * g.tangentNorm z v ≤ h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ∧
        h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ≤ lambda⁻¹ * g.tangentNorm z v)
    (hfb : ∀ z, k.edist q z ≤ ENNReal.ofReal (4 * (L + 1)) →
      ∀ v : TangentSpace (𝓡 3) z,
        lambda * k.tangentNorm z v ≤ h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ∧
        h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ lambda⁻¹ * k.tangentNorm z v)
    (hdom : {z | g.edist p z ≤ ENNReal.ofReal R} ⊆ (e.trans f.symm).source)
    (himage : MapsTo (e.trans f.symm) {z | g.edist p z ≤ ENNReal.ofReal R}
      {z | k.edist q z ≤ ENNReal.ofReal L}) :
    ∀ x, g.edist p x ≤ ENNReal.ofReal R →
      ∀ y, g.edist p y ≤ ENNReal.ofReal R →
        ENNReal.ofReal (lambda ^ 2) * g.edist x y ≤
          k.edist ((e.trans f.symm) x) ((e.trans f.symm) y) ∧
        k.edist ((e.trans f.symm) x) ((e.trans f.symm) y) ≤
          ENNReal.ofReal (lambda⁻¹ ^ 2) * g.edist x y := by
  intro x hx y hy
  have hE := terminalCommonInterval_buffered_distance g h hg e he hei p hR hlambda
    hes heb x hx y hy
  have hF := terminalCommonInterval_buffered_distance k h hk f hf hfi q hL hlambda
    hfs hfb ((e.trans f.symm) x) (himage hx) ((e.trans f.symm) y) (himage hy)
  have hactual (z : M) (hz : z ∈ (e.trans f.symm).source) :
      f ((e.trans f.symm) z) = e z := f.right_inv hz.2
  rw [hactual x (hdom hx), hactual y (hdom hy)] at hF
  have hinv : 0 < lambda⁻¹ := inv_pos.mpr hlambda
  have hcancel : ENNReal.ofReal lambda * ENNReal.ofReal lambda⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hlambda.le, mul_inv_cancel₀ hlambda.ne', ENNReal.ofReal_one]
  have hcancel' : ENNReal.ofReal lambda⁻¹ * ENNReal.ofReal lambda = 1 := by
    rw [mul_comm, hcancel]
  constructor
  · calc
      _ = ENNReal.ofReal lambda * (ENNReal.ofReal lambda * g.edist x y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hlambda.le, ← pow_two]
      _ ≤ ENNReal.ofReal lambda * (ENNReal.ofReal lambda⁻¹ *
          k.edist ((e.trans f.symm) x) ((e.trans f.symm) y)) :=
        mul_le_mul_right (hE.1.trans hF.2) _
      _ = _ := by rw [← mul_assoc, hcancel, one_mul]
  · calc
      _ = ENNReal.ofReal lambda⁻¹ * (ENNReal.ofReal lambda *
          k.edist ((e.trans f.symm) x) ((e.trans f.symm) y)) := by
        rw [← mul_assoc, hcancel', one_mul]
      _ ≤ ENNReal.ofReal lambda⁻¹ * (ENNReal.ofReal lambda⁻¹ * g.edist x y) :=
        mul_le_mul_right (hF.1.trans hE.2) _
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hinv.le, ← pow_two]

end PoincareConjecture.M47
