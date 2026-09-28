import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateError
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem m64FreePhase_boundary_zero_trace_extension
    {u C : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (ha : a 1 = 0)
    (hu : Continuous u) (hC : ContDiff ℝ 1 C)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j)
      (fun p => u p j) (ball a R))
    (htrace : ∀ p ∈ closedBall a R, p 1 ≤ 0 → u p = C p) :
    ∃ (v : LoopPlane → E) (dv : Fin 2 → LoopPlane → E),
      Continuous v ∧ HasCompactSupport v ∧
      (∀ p : LoopPlane, p 1 < 0 → v p = 0) ∧
      (∀ i, MemLp (dv i) 2 volume) ∧
      (∀ i j, HasWeakPartialDeriv i (fun p => dv i p j)
        (fun p => v p j) univ) ∧
      (∀ j : Fin n, MemW01p 2 (fun p => v p j)
        {p : LoopPlane | 0 < p 1}) ∧
      ∀ p ∈ ball a (R / 2),
        v p = u p - C p ∧
          ∀ i, dv i p = W i p - fderiv ℝ C p (EuclideanSpace.single i 1) := by
  let error : LoopPlane → E := fun p => u p - C p
  let D : Fin 2 → LoopPlane → E := fun i p =>
    W i p - fderiv ℝ C p (EuclideanSpace.single i 1)
  obtain ⟨hm, hD, hd⟩ := m64BoundaryCoordinate_error_columns
    hu.continuousOn hC hW hw
  obtain ⟨chi, hchi, hcompact, hsupport, hone, htests⟩ :=
    m64WeakBoundaryError_localization
      (u := error) (V := D) hR ha
      (hu.sub hC.continuous).continuousOn hm hD hd
      (fun p hp hp1 => by
        dsimp only [error]
        rw [htrace p hp hp1, sub_self])
  let v : LoopPlane → E := fun p => chi p • error p
  let dv : Fin 2 → LoopPlane → E := fun i p =>
    chi p • D i p + fderiv ℝ chi p (EuclideanSpace.single i 1) • error p
  have hv : Continuous v := hchi.continuous.smul (hu.sub hC.continuous)
  have hvc : HasCompactSupport v := hcompact.smul_right
  have hvzero : ∀ p : LoopPlane, p 1 < 0 → v p = 0 := by
    intro p hp
    by_cases hpt : p ∈ tsupport chi
    · change chi p • error p = 0
      rw [show error p = 0 by
        dsimp only [error]
        rw [htrace p (ball_subset_closedBall (hsupport hpt)) hp.le, sub_self]]
      simp
    · simp [v, image_eq_zero_of_notMem_tsupport hpt]
  have hdv (i : Fin 2) : MemLp (dv i) 2 volume := by
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [dv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      ((htests j).2 i).1
  have hdweak (i : Fin 2) (j : Fin n) :
      HasWeakPartialDeriv i (fun p => dv i p j) (fun p => v p j) univ := by
    simpa only [v, dv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      ((htests j).2 i).2
  have hvzero_mem (j : Fin n) : MemW01p 2 (fun p => v p j)
      {p : LoopPlane | 0 < p 1} := by
    have hvLp : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hvc
    have hvcj : HasCompactSupport (fun p => v p j) := by
      change HasCompactSupport ((EuclideanSpace.proj (𝕜 := ℝ) j) ∘ v)
      exact hvc.comp_left (EuclideanSpace.proj (𝕜 := ℝ) j).map_zero
    have hwit : MemW1pWitness 2 (fun p => v p j) univ := {
      memLp := by
        simpa only [Measure.restrict_univ] using MemLp.eval_piLp hvLp j
      weakGrad := fun p => WithLp.toLp 2 (fun i => dv i p j)
      weakGrad_component_memLp := fun i => by
        simpa only [Measure.restrict_univ] using
          MemLp.eval_piLp (hdv i) j
      isWeakGrad := fun i => hdweak i j }
    exact m64MemW01p_of_halfspace_support hwit hvcj 1 (fun p hp =>
      congrArg (fun z : E => z j) (hvzero p hp))
  refine ⟨v, dv, hv, hvc, hvzero, hdv, hdweak, ?_, ?_⟩
  · intro j
    exact hvzero_mem j
  · intro p hp
    have heq := hone p hp
    refine ⟨?_, ?_⟩
    · simp only [v, heq.1, one_smul, error]
    · intro i
      simp [dv, heq.1, heq.2, D]

end PoincareConjecture
