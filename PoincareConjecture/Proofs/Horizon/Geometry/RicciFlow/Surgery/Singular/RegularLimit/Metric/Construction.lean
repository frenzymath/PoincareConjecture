import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def tangentBilinearChartCoefficients
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (q : M) (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := by
  let c := extChartAt (𝓡 n) q
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (c.symm z)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (c.symm z)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let A := mfderiv (𝓡 n) (𝓡 n) c.symm z
  exact ContinuousLinearMap.bilinearComp (B (c.symm z)) A A

omit [IsManifold (𝓡 n) ∞ M] in
theorem tangentBilinearChartCoefficients_apply
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (q : M) (z v w : EuclideanSpace ℝ (Fin n)) :
    tangentBilinearChartCoefficients B q z v w =
      B ((extChartAt (𝓡 n) q).symm z)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z w) := rfl

theorem tangentBilinear_inCoordinates
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (q y : M) (hy : y ∈ (extChartAt (𝓡 n) q).source) :
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M => TangentSpace (𝓡 n) x →L[ℝ] ℝ) q y q y (B y) =
        tangentBilinearChartCoefficients B q (extChartAt (𝓡 n) q y) := by
  have hyt : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q).baseSet := by simpa using hy
  have hD : (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q).symmL ℝ y =
        mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm
          (extChartAt (𝓡 n) q y) := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (TangentBundle.symmL_trivializationAt (I := 𝓡 n) (by simpa using hy))
  ext v w
  rw [inCoordinates_apply_eq₂ hyt hyt (by simp)]
  rw [← Trivialization.symmL_apply (R := ℝ) _ hyt v,
    ← Trivialization.symmL_apply (R := ℝ) _ hyt w, hD]
  rw [tangentBilinearChartCoefficients_apply]
  have hB : (B ((extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q y)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) = B y := by
    change M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ at B
    exact congrArg B ((extChartAt (𝓡 n) q).left_inv hy)
  rw [hB]
  simp [Trivialization.linearMapAt_def_of_mem]
  rfl

theorem contMDiff_tangentBilinear_of_chartCoefficients
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (hsmooth : ∀ q : M, ContDiffAt ℝ ∞ (tangentBilinearChartCoefficients B q)
      (extChartAt (𝓡 n) q q)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        x (B x)) := by
  intro q
  rw [Bundle.contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have hcomp := (hsmooth q).contMDiffAt.comp q
    (contMDiffAt_extChartAt (I := 𝓡 n) (n := ∞) (x := q))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓡 n) q).mem_nhds
    (mem_extChartAt_source q)] with y hy
  exact tangentBilinear_inCoordinates B q y hy

def metricOfChartCoefficients
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hsmooth : ∀ q : M, ContDiffAt ℝ ∞ (tangentBilinearChartCoefficients B q)
      (extChartAt (𝓡 n) q q)) : RiemannianMetric n M where
  inner := B
  symm := hsymm
  pos := hpos
  isVonNBounded x := by
    let E := EuclideanSpace ℝ (Fin n)
    obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound
      (B := fun _ : E => (B x : E →L[ℝ] E →L[ℝ] ℝ))
      (K := {(0 : E)}) isCompact_singleton continuousOn_const (fun _ _ => hpos x)
    change Bornology.IsVonNBounded ℝ {v : E | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ E (c⁻¹ + 1)).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖v‖ ^ 2 < c⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hc]
      rw [mul_comm]
      exact (hbound 0 (mem_singleton 0) v).trans_lt hv
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  contMDiff := contMDiff_tangentBilinear_of_chartCoefficients B hsmooth

theorem metricOfChartCoefficients_inner
    (B : ∀ x : M, TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hsmooth : ∀ q : M, ContDiffAt ℝ ∞ (tangentBilinearChartCoefficients B q)
      (extChartAt (𝓡 n) q q)) (x : M) :
    (metricOfChartCoefficients B hsymm hpos hsmooth).inner x = B x := rfl

end PoincareConjecture.SingularRegularLimit
