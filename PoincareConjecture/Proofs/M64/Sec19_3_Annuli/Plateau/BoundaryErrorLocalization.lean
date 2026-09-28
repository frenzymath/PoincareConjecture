import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceApproximation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAbsorption

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64WeakBoundaryError_localization
    {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (ha : a 1 = 0)
    (hu : ContinuousOn u (closedBall a R))
    (hup : MemLp u 2 (volume.restrict (ball a R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (ball a R))
    (hzero : ∀ p ∈ closedBall a R, p 1 ≤ 0 → u p = 0) :
    ∃ chi : LoopPlane → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ ball a R ∧
      (∀ p ∈ ball a (R / 2), chi p = 1 ∧ fderiv ℝ chi p = 0) ∧
      ∀ j : Fin m,
        MemW01p 2 (fun p => chi p * u p j) {p : LoopPlane | 0 < p 1} ∧
        ∀ i : Fin 2,
          MemLp (fun p => chi p * V i p j +
            fderiv ℝ chi p (EuclideanSpace.single i 1) * u p j) 2 volume ∧
          HasWeakPartialDeriv i
            (fun p => chi p * V i p j +
              fderiv ℝ chi p (EuclideanSpace.single i 1) * u p j)
            (fun p => chi p * u p j) univ := by
  have hcenter : u a = 0 := hzero a (mem_closedBall_self hR.le) ha.le
  obtain ⟨chi, hc, hcompact, hsupport, hone, hdata⟩ :=
    M60.suWeakMap_localization (by norm_num : (1 : ℝ) < 2) (half_lt_self hR)
      hu (by simpa using hup) (fun i => by simpa using hV i) hw
  have hdata' (j : Fin m) :
      Continuous (fun p => chi p * u p j) ∧ HasCompactSupport (fun p => chi p * u p j) ∧
      MemLp (fun p => chi p * u p j) 2 volume ∧
      ∀ i : Fin 2,
        MemLp (fun p => chi p * V i p j +
          fderiv ℝ chi p (EuclideanSpace.single i 1) * u p j) 2 volume ∧
        HasWeakPartialDeriv i
          (fun p => chi p * V i p j +
            fderiv ℝ chi p (EuclideanSpace.single i 1) * u p j)
          (fun p => chi p * u p j) univ := by
    simpa only [hcenter, PiLp.zero_apply, sub_zero, ENNReal.ofReal_ofNat] using hdata j
  refine ⟨chi, hc, hcompact, hsupport, hone, ?_⟩
  intro j
  let w : MemW1pWitness 2 (fun p => chi p * u p j) univ := {
    memLp := by simpa only [Measure.restrict_univ] using (hdata' j).2.2.1
    weakGrad := fun p => WithLp.toLp 2 (fun i => chi p * V i p j +
      fderiv ℝ chi p (EuclideanSpace.single i 1) * u p j)
    weakGrad_component_memLp := fun i => by
      simpa only [Measure.restrict_univ] using ((hdata' j).2.2.2 i).1
    isWeakGrad := fun i => ((hdata' j).2.2.2 i).2 }
  refine ⟨m64MemW01p_of_halfspace_support w (hdata' j).2.1 1 ?_, (hdata' j).2.2.2⟩
  intro p hp
  by_cases hpS : p ∈ tsupport chi
  · rw [hzero p (ball_subset_closedBall (hsupport hpS)) hp.le]
    simp
  · rw [image_eq_zero_of_notMem_tsupport hpS, zero_mul]

end PoincareConjecture
