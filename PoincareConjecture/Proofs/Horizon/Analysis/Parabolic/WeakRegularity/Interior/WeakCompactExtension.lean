




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Producer
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










open Set Filter MeasureTheory MeasureTheory.Measure Metric
open scoped Topology ContDiff

set_option maxHeartbeats 1000000

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Parabolic.WeakRegularity
open Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

local instance : Measure.IsAddHaarMeasure (volume : Measure (Spacetime n)) := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance




theorem exists_weak_compact_extension
    (hU : IsOpen U) {C : Coefficients n} (hC : C.IsSmoothOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U) :
    ∃ (V : Set (Spacetime n)) (C' : Coefficients n) (u' : Spacetime n → ℝ),
      IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      C'.IsSmoothOn (Set.univ : Set (Spacetime n)) ∧
      (∀ i j, HasCompactSupport (C'.principal i j)) ∧
      (∀ i, HasCompactSupport (C'.drift i)) ∧
      HasCompactSupport C'.zeroth ∧ Continuous u' ∧ HasCompactSupport u' ∧
      (∀ i j, EqOn (C'.principal i j) (C.principal i j) V) ∧
      (∀ i, EqOn (C'.drift i) (C.drift i) V) ∧
      EqOn C'.zeroth C.zeroth V ∧ EqOn u' u V ∧
      WeakSolutionOn C' u' V := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let χ : ContDiffBump z :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let V : Set (Spacetime n) := ball z χ.rIn
  have hV : IsOpen V := isOpen_ball
  have hzV : z ∈ V := mem_ball_self χ.rIn_pos
  have hVU : V ⊆ U := by
    intro y hy
    apply hδU
    exact lt_trans hy (by change δ / 4 < δ; linarith)
  have hχU : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro y hy
    apply hδU
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (by
      change δ / 2 < δ
      linarith)
  let ext (q : Spacetime n → ℝ) : Spacetime n → ℝ := fun y => χ y * q y
  have ext_smooth {q : Spacetime n → ℝ} (hq : ContDiffOn ℝ ∞ q U) :
      ContDiff ℝ ∞ (ext q) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (ext q)
    · have hyU : y ∈ U := hχU (tsupport_mul_subset_left hy)
      exact χ.contDiff.contDiffAt.mul ((hq y hyU).contDiffAt (hU.mem_nhds hyU))
    · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
  have ext_continuous {q : Spacetime n → ℝ} (hq : ContinuousOn q U) :
      Continuous (ext q) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ tsupport (ext q)
    · have hyU : y ∈ U := hχU (tsupport_mul_subset_left hy)
      exact χ.continuous.continuousAt.mul (hq.continuousAt (hU.mem_nhds hyU))
    · exact continuousAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
  have ext_eq {q : Spacetime n → ℝ} : EqOn (ext q) q V := by
    intro y hy
    simp only [ext, χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have ext_support {q : Spacetime n → ℝ} : HasCompactSupport (ext q) :=
    χ.hasCompactSupport.mul_right
  let C' : Coefficients n :=
    { principal := fun i j => ext (C.principal i j)
      drift := fun i => ext (C.drift i)
      zeroth := ext C.zeroth }
  let u' := ext u
  have hC'smooth : C'.IsSmoothOn (Set.univ : Set (Spacetime n)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      exact ext_smooth (hC.1 i j) |>.contDiffOn
    · intro i
      exact ext_smooth (hC.2.1 i) |>.contDiffOn
    · exact ext_smooth hC.2.2 |>.contDiffOn
  have hWeak : WeakSolutionOn C' u' V := by
    have hzero {g : Spacetime n → ℝ} {y : Spacetime n} (hy : y ∉ tsupport g)
        (v : Spacetime n) : fderiv ℝ g y v = 0 := by
      have he : g =ᶠ[𝓝 y] (fun _ : Spacetime n => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp hy
      have he' : fderiv ℝ g y =
          fderiv ℝ (fun _ : Spacetime n => (0 : ℝ)) y := he.fderiv_eq
      have hzderiv : fderiv ℝ (fun _ : Spacetime n => (0 : ℝ)) y = 0 := by
        exact fderiv_const_apply (𝕜 := ℝ) (E := Spacetime n) (F := ℝ)
          (x := y) (0 : ℝ)
      rw [hzderiv] at he'
      exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A v) he'
    have hadj_zero {K : Coefficients n} {φ : Spacetime n → ℝ}
        {y : Spacetime n} (hy : y ∉ tsupport φ) : K.adjoint φ y = 0 := by
      simp only [Coefficients.adjoint]
      have hφ : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      have ht : timeDeriv φ y = 0 := hzero (g := φ) hy (0, 1)
      have hs (i : Fin n) : spatialDeriv i φ y = 0 := hzero (g := φ) hy _
      have hss (i j : Fin n) :
          spatialDeriv j (spatialDeriv i (fun x => K.principal i j x * φ x)) y = 0 := by
        apply hzero
        intro h
        apply hy
        exact (tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans
          (tsupport_mul_subset_right) h
      have hsd (i : Fin n) :
          spatialDeriv i (fun x => K.drift i x * φ x) y = 0 := by
        have hmul : tsupport (fun x => K.drift i x * φ x) ⊆ tsupport φ :=
          tsupport_mul_subset_right
        exact hzero (g := fun x => K.drift i x * φ x) (fun h => hy (hmul h)) _
      simp only [hφ, ht, hs, hss, hsd, Finset.sum_const_zero, zero_add,
        sub_zero, zero_sub, mul_zero]
      ring
    have hfeq {a b : Spacetime n → ℝ} (hab : EqOn a b V) (y : Spacetime n)
        (hy : y ∈ V) (v : Spacetime n) : fderiv ℝ a y v = fderiv ℝ b y v := by
      exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A v)
        (hab.eventuallyEq_of_mem (hV.mem_nhds hy)).fderiv_eq
    have hadj_eq {φ : Spacetime n → ℝ} {y : Spacetime n} (hy : y ∈ V) :
        C'.adjoint φ y = C.adjoint φ y := by
      have hP (i j : Fin n) :
          EqOn (fun x => C'.principal i j x * φ x)
            (fun x => C.principal i j x * φ x) V := by
        intro x hx
        change C'.principal i j x * φ x = C.principal i j x * φ x
        rw [show C'.principal i j x = C.principal i j x from ext_eq hx]
      have hD (i : Fin n) :
          EqOn (fun x => C'.drift i x * φ x)
            (fun x => C.drift i x * φ x) V := by
        intro x hx
        change C'.drift i x * φ x = C.drift i x * φ x
        rw [show C'.drift i x = C.drift i x from ext_eq hx]
      have hp (i j : Fin n) :
          spatialDeriv j (spatialDeriv i (fun x => C'.principal i j x * φ x)) y =
            spatialDeriv j (spatialDeriv i (fun x => C.principal i j x * φ x)) y :=
        hfeq (fun x hx => hfeq (hP i j) x hx (spatialDirection i)) y hy
          (spatialDirection j)
      have hd' (i : Fin n) :
          spatialDeriv i (fun x => C'.drift i x * φ x) y =
            spatialDeriv i (fun x => C.drift i x * φ x) y :=
        hfeq (hD i) y hy (spatialDirection i)
      have hsumP :
          (∑ i, ∑ j, spatialDeriv j (spatialDeriv i
            (fun x => C'.principal i j x * φ x)) y) =
            ∑ i, ∑ j, spatialDeriv j (spatialDeriv i
              (fun x => C.principal i j x * φ x)) y := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hp i j
      have hsumD :
          (∑ i, spatialDeriv i (fun x => C'.drift i x * φ x) y) =
            ∑ i, spatialDeriv i (fun x => C.drift i x * φ x) y := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hd' i
      simp only [Coefficients.adjoint]
      rw [hsumP, hsumD, show C'.zeroth y = C.zeroth y from ext_eq hy]
    have hu'cont : Continuous u' := ext_continuous hu
    refine ⟨hu'cont.continuousOn.locallyIntegrableOn hV.measurableSet, ?_⟩
    intro φ hφ hφc hφV
    have hφU : tsupport φ ⊆ U := hφV.trans hVU
    have horig := hw.2 φ hφ hφc hφU
    rw [← horig]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ V
    · change ext u y * C'.adjoint φ y = u y * C.adjoint φ y
      rw [ext_eq hy, hadj_eq hy]
    · rw [hadj_zero (K := C') (φ := φ) (fun h => hy (hφV h)),
        hadj_zero (K := C) (φ := φ) (fun h => hy (hφV h))]
      simp only [mul_zero]
  refine ⟨V, C', u', hV, hzV, hVU, hC'smooth, ?_, ?_, ?_,
    ext_continuous hu, ext_support, ?_, ?_, ?_, ext_eq, hWeak⟩
  · intro i j
    exact ext_support
  · intro i
    exact ext_support
  · exact ext_support
  · intro i j
    exact ext_eq
  · intro i
    exact ext_eq
  · exact ext_eq

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
