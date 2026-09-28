import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalZeroExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoefficientTests

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

theorem m64NaturalGrowth_face_boundary_test
    (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hFzero : ∀ i p, p 1 ≤ 0 → F i p = 0)
    (hbzero : ∀ p, p 1 ≤ 0 → b p = 0)
    (hu : Continuous u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ O)
    (hup : MemLp u 2 volume) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : dirichlet → ∀ p : LoopPlane, p 1 = 0 → u p = 0)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p) :
    (∫ p, ∑ i : Fin 2, F i p * du i p) = ∫ p, b p * u p := by
  classical
  by_cases hD : dirichlet
  · let H : Set LoopPlane := {p | 0 < p 1}
    have hH : IsOpen H := isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
    have hsupport : support (H.indicator u) ⊆ support u := by
      intro p hp
      by_cases hh : p ∈ H
      · simpa only [mem_support, indicator_of_mem hh] using hp
      · simp only [mem_support, indicator_of_notMem hh, ne_eq, not_true_eq_false] at hp
    have hts : tsupport (H.indicator u) ⊆ tsupport u := closure_mono hsupport
    have hh := m64NaturalGrowth_mixed_boundary_test True hO hF hb
      (m64Continuous_normalZeroExtension_continuous hu (hzero hD))
      (hc.mono hsupport) (hts.trans hs)
      ((memLp_indicator_iff_restrict hH.measurableSet).mpr (hup.restrict H))
      (fun i => (memLp_indicator_iff_restrict hH.measurableSet).mpr ((hdu i).restrict H))
      (fun i => m64Continuous_normalZeroExtension_weak i hu (hzero hD)
        (hup.restrict H) ((hdu i).restrict H) ((hw i).restrict hH (subset_univ H)))
      (fun _ p hp => indicator_of_notMem (show p ∉ H from not_lt.mpr hp.le) u)
      (fun phi hp hpc hps hpf => heq phi hp hpc hps (fun _ => hpf trivial))
    have hleft : (fun p => ∑ i : Fin 2, F i p * H.indicator (du i) p) =
        fun p => ∑ i : Fin 2, F i p * du i p := by
      funext p
      by_cases hp : p ∈ H
      · simp only [indicator_of_mem hp]
      · have hp0 : p 1 ≤ 0 := le_of_not_gt hp
        simp only [hFzero _ p hp0, zero_mul, Finset.sum_const_zero]
    have hright : (fun p => b p * H.indicator u p) = fun p => b p * u p := by
      funext p
      by_cases hp : p ∈ H
      · simp only [indicator_of_mem hp]
      · rw [hbzero p (le_of_not_gt hp), zero_mul, zero_mul]
    rwa [hleft, hright] at hh
  · exact m64NaturalGrowth_mixed_boundary_test dirichlet hO hF hb hu hc hs hup hdu hw
      (fun hd => (hD hd).elim) heq

theorem m64NaturalGrowth_coefficient_face_test
    {n : ℕ} (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hFzero : ∀ i p, p 1 ≤ 0 → F i p = 0)
    (hbzero : ∀ p, p 1 ≤ 0 → b p = 0)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} (hu : Continuous u)
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 < C)
    (hdf : ∀ z : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f z‖ ≤ C)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O)
    (hz : dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p * f (u p) = 0)
    (heq : ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * psi p) :
    (∫ p, ∑ i : Fin 2, F i p * (phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p))) =
      ∫ p, b p * (phi p * f (u p)) := by
  have ht := m64CompactCoefficientTest_weak_derivatives hu hV hw hf hC hdf hp hc
  have hcont := hp.continuous.mul (hf.continuous.comp hu)
  exact m64NaturalGrowth_face_boundary_test dirichlet hO hF hb hFzero hbzero hcont
    hc.mul_right (tsupport_mul_subset_left.trans hs)
    (hcont.memLp_of_hasCompactSupport hc.mul_right) (fun i => (ht i).1)
    (fun i => (ht i).2) hz heq

end PoincareConjecture
