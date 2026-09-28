import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryReflectedEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakClassical

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

def m64ContinuousBoundaryReflect (epsilon : ℝ) (u : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  if 0 ≤ p 0 then u p else epsilon * u (reflect p)

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

theorem m64ContinuousBoundaryReflect_eq_on_closedHalfSpace
    (epsilon : ℝ) (u : LoopPlane → ℝ) :
    EqOn (m64ContinuousBoundaryReflect epsilon u) u {p : LoopPlane | 0 ≤ p 0} := by
  intro p hp
  change 0 ≤ p 0 at hp
  simp only [m64ContinuousBoundaryReflect, if_pos hp]

theorem m64ContinuousBoundaryReflect_memLp {u : LoopPlane → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict (halfSpace 2))) (epsilon : ℝ) :
    MemLp (m64ContinuousBoundaryReflect epsilon u) p volume :=
  (memLp_congr_ae (m64ContinuousBoundaryReflect_ae epsilon u)).mpr
    (m64BoundaryReflect_memLp hu epsilon)

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

end PoincareConjecture
