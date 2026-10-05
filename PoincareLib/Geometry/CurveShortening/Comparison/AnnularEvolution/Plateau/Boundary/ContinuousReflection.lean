import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ReflectedEquation
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Weak.Classical

/-!
# Continuous representatives of reflected boundary maps

The weak reflection sets the null face to zero. The continuous reflection
instead retains the original trace, without changing any weak derivative
or integral. This is the representative used by the interior C1 theorem.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareMT

/-- The signed boundary reflection retains the literal trace on the closed positive
half-plane. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
def m64ContinuousBoundaryReflect (epsilon : ℝ) (u : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  if 0 ≤ p 0 then u p else epsilon * u (reflect p)

/-- Agreement of the two literal face traces makes the signed reflection continuous. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
theorem m64ContinuousBoundaryReflect_continuous {u : LoopPlane → ℝ}
    (hu : Continuous u) (epsilon : ℝ)
    (hface : ∀ p : LoopPlane, p 0 = 0 → u p = epsilon * u p) :
    Continuous (m64ContinuousBoundaryReflect epsilon u) := by
  apply hu.if_le (continuous_const.mul (hu.comp reflect.continuous)) continuous_const
    (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
  intro p hp
  change 0 = p 0 at hp
  have hr : reflect p = p := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [hp.symm]
    · exact reflect_apply_ne p i hi
  change u p = epsilon * u (reflect p)
  rw [hr]
  exact hface p hp.symm

/-- The continuous reflection differs from the weak reflection only on the null boundary
face. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
theorem m64ContinuousBoundaryReflect_ae (epsilon : ℝ) (u : LoopPlane → ℝ) :
    m64ContinuousBoundaryReflect epsilon u =ᵐ[volume] m64BoundaryReflect epsilon u := by
  have hcoord : ∀ᵐ p : LoopPlane ∂volume, p 0 ≠ 0 :=
    (PiLp.volume_preserving_ofLp (ι := Fin 2)).quasiMeasurePreserving.tendsto_ae.eventually
      (Measure.ae_eval_ne (fun _ : Fin 2 => volume) 0 (0 : ℝ))
  filter_upwards [hcoord] with p hp
  by_cases hpos : 0 < p 0
  · have hneg : ¬ 0 < -p 0 := by linarith
    simp [m64ContinuousBoundaryReflect, m64BoundaryReflect, halfSpace, hpos, hpos.le, hneg]
  · have hneg : p 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hp
    have hpneg : 0 < -p 0 := neg_pos.mpr hneg
    simp [m64ContinuousBoundaryReflect, m64BoundaryReflect, halfSpace, hpos,
      not_le.mpr hneg, hpneg]

/-- The continuous reflection equals the original function throughout the closed positive
half-plane. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
theorem m64ContinuousBoundaryReflect_eq_on_closedHalfSpace
    (epsilon : ℝ) (u : LoopPlane → ℝ) :
    EqOn (m64ContinuousBoundaryReflect epsilon u) u {p : LoopPlane | 0 ≤ p 0} := by
  intro p hp
  change 0 ≤ p 0 at hp
  simp only [m64ContinuousBoundaryReflect, if_pos hp]

/-- The actual continuous reflection retains the half-plane Lp bound. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
theorem m64ContinuousBoundaryReflect_memLp {u : LoopPlane → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict (halfSpace 2))) (epsilon : ℝ) :
    MemLp (m64ContinuousBoundaryReflect epsilon u) p volume :=
  (memLp_congr_ae (m64ContinuousBoundaryReflect_ae epsilon u)).mpr
    (m64BoundaryReflect_memLp hu epsilon)

/-- The even continuous representative has the actual reflected weak columns with the
coordinate signs. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary
analysis. -/
theorem m64EvenBoundaryReflect_weak {u v : LoopPlane → ℝ} (i : Fin 2)
    (hu : MemLp u 2 (volume.restrict (halfSpace 2)))
    (hv : MemLp v 2 (volume.restrict (halfSpace 2)))
    (hw : HasWeakPartialDeriv i v u (halfSpace 2)) :
    HasWeakPartialDeriv i (m64BoundaryReflect (coordinateSign i) v)
      (m64ContinuousBoundaryReflect 1 u) univ := by
  have hh := hasWeakPartialDeriv_evenReflect (by norm_num : (1 : ℝ≥0∞) ≤ 2) i hu hv hw
  have hae : m64ContinuousBoundaryReflect 1 u =ᵐ[volume.restrict univ] evenReflect u := by
    simp only [Measure.restrict_univ]
    filter_upwards [m64ContinuousBoundaryReflect_ae 1 u] with p hp
    simpa only [m64BoundaryReflect, one_mul, evenReflect] using hp
  exact M60.suWeakPartial_congr_ae hh hae EventuallyEq.rfl

end PoincareMT
