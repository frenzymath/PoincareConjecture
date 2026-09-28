import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakDerivatives
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.HilbertSubsequence
import PoincareConjecture.Proofs.M03.Existence.EuclideanGraphRellichNative
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2












set_option autoImplicit false

open MeasureTheory Filter Set
open scoped Topology SchwartzMap LineDeriv InnerProductSpace ENNReal

namespace PoincareConjecture

open EuclideanTranslationNative EuclideanRellichNative EuclideanGraphRellichNative
  EuclideanMollificationNative





theorem m65C1L2_weak_subsequence {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ n, ContDiff ℝ 1 (f n)) (hfL2 : ∀ n, MemLp (f n) 2 volume)
    (hdL2 : ∀ n (i : Fin d),
      MemLp (fun x => fderiv ℝ (f n) x
        (EuclideanSpace.single i (1 : ℝ))) 2 volume)
    (hsupport : ∀ n x, x ∉ K → f n x = 0)
    {R D : ℝ} (hD : 0 ≤ D)
    (hvalue : ∀ n, ‖(hfL2 n).toLp (f n)‖ ≤ R)
    (hgradient : ∀ n, gradientEnergy (f n) ≤ D ^ 2) :
    ∃ (phi : ℕ → ℕ) (u0 : ScalarL2 d) (d0 : PiLp 2 (fun _ : Fin d => ScalarL2 d)),
      StrictMono phi ∧ ‖u0‖ ≤ R ∧ ‖d0‖ ≤ D ∧
      Tendsto (fun n => (hfL2 (phi n)).toLp (f (phi n))) atTop (𝓝 u0) ∧
      (∀ w : PiLp 2 (fun _ : Fin d => ScalarL2 d),
        Tendsto (fun n => ⟪WithLp.toLp 2 (fun i => (hdL2 (phi n) i).toLp
          (fun x => fderiv ℝ (f (phi n)) x
            (EuclideanSpace.single i (1 : ℝ)))), w⟫_ℝ)
          atTop (𝓝 ⟪d0, w⟫_ℝ)) ∧
      ∀ (i : Fin d) (test : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)),
        ⟪d0 i, test.toLp 2 volume⟫_ℝ =
          -⟪u0, (∂_{EuclideanSpace.single i (1 : ℝ)} test).toLp 2 volume⟫_ℝ := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let values (n : ℕ) : ScalarL2 d := (hfL2 n).toLp (f n)
  let derivatives (n : ℕ) : PiLp 2 (fun _ : Fin d => ScalarL2 d) :=
    WithLp.toLp 2 (fun i => (hdL2 n i).toLp
      (fun x => fderiv ℝ (f n) x (EuclideanSpace.single i (1 : ℝ))))
  have hcompact : IsCompact (closure (range values)) := by
    apply isCompact_closure_supported_C1 hK hD (R := R)
    · rintro _ ⟨n, rfl⟩
      exact hvalue n
    · rintro _ ⟨n, rfl⟩
      exact ⟨f n, hf n, hfL2 n, hdL2 n, hsupport n, rfl, hgradient n⟩
  obtain ⟨u0, _, phi1, hphi1, hstrong1⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hderivative_bound (n : ℕ) : ‖derivatives n‖ ≤ D := by
    apply (sq_le_sq₀ (norm_nonneg _) hD).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i, ‖(hdL2 n i).toLp
      (fun x => fderiv ℝ (f n) x (EuclideanSpace.single i (1 : ℝ)))‖ ^ 2) ≤ D ^ 2
    rw [← gradientEnergy_eq_sum_norm_sq]
    exact hgradient n
  obtain ⟨d0, phi2, hphi2, hd0, hweak⟩ :=
    InnerProductSpace.exists_subsequence_tendsto_inner_of_norm_bound
      (fun n => derivatives (phi1 n)) (fun n => hderivative_bound (phi1 n))
  let phi := phi1 ∘ phi2
  have hstrong : Tendsto (fun n => values (phi n)) atTop (𝓝 u0) :=
    hstrong1.comp hphi2.tendsto_atTop
  have hu0 : ‖u0‖ ≤ R :=
    le_of_tendsto hstrong.norm (Eventually.of_forall fun n => hvalue (phi n))
  refine ⟨phi, u0, d0, hphi1.comp hphi2, hu0, hd0, hstrong, hweak, ?_⟩
  intro i test
  let testLp := test.toLp 2 volume
  have hsingle (w : PiLp 2 (fun _ : Fin d => ScalarL2 d)) :
      ⟪w, PiLp.single 2 i testLp⟫_ℝ = ⟪w i, testLp⟫_ℝ := by
    simp only [PiLp.inner_apply, PiLp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hdtest : Tendsto (fun n => ⟪derivatives (phi n) i, testLp⟫_ℝ)
      atTop (𝓝 ⟪d0 i, testLp⟫_ℝ) := by
    simpa only [hsingle, phi, Function.comp_def] using hweak (PiLp.single 2 i testLp)
  have heq (n : ℕ) : ⟪derivatives (phi n) i, testLp⟫_ℝ =
      -⟪values (phi n), (∂_{EuclideanSpace.single i (1 : ℝ)} test).toLp 2 volume⟫_ℝ :=
    m65C1L2_testDerivative (hf (phi n)) (hfL2 (phi n))
      (EuclideanSpace.single i (1 : ℝ)) (hdL2 (phi n) i) test
  simp only [heq] at hdtest
  exact tendsto_nhds_unique hdtest (hstrong.inner tendsto_const_nhds).neg

end PoincareConjecture
