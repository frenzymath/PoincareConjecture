import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DilatedIntegralHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SmoothInitialHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.UnforcedHeatUniqueness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem contDiffAt_weak_time_dilation
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {a b T B : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b) (hT : 0 < T)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    (hsmall : ‖(formWeakHeatOperator J hc hd hi hn hT.le).comp
      (normalizedDilationLp J ha.le (ha1.trans h1b).le hT.le hBT hB A hA 1)‖ < 1)
    (v : ℝ → V) (hv : MemLp v 2 (timeMeasure B)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 B))
    (hgraph : ∀ᵐ t ∂timeMeasure B, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 B, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ r in (0 : ℝ)..t, A r (v r)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiffAt ℝ ∞ (fun s => U (s * t)) 1 := by
  let M := normalizedDilationLp J ha.le (ha1.trans h1b).le hT.le hBT hB A hA
  have hMc : ContDiffAt ℝ ∞ M 1 :=
    (contDiffOn_normalizedDilationLp J ha.le (ha1.trans h1b) hT.le hBT hB A hA).contDiffAt
      (Icc_mem_nhds ha1 h1b)
  have hKc : ContinuousAt (fun s => (formWeakHeatOperator J hc hd hi hn hT.le).comp (M s)) 1 :=
    continuousAt_const.clm_comp hMc.continuousAt
  have hnew := contDiffAt_affineInitialValue J hc hd hi hn hT.le M (fun _ : ℝ => 0)
    (U 0) hMc contDiffAt_const hsmall ht
  apply hnew.congr_of_eventuallyEq
  filter_upwards [hKc.norm.eventually (gt_mem_nhds hsmall), Icc_mem_nhds ha1 h1b] with s hs hsmem
  obtain ⟨w, hWc, hWg, hWi⟩ := exists_dilated_integral_heat J ha (ha1.trans h1b).le
    hT.le hBT hB A hA v hv U hU hgraph heq hsmem
  let z := affineInitialForm J hc hd hi hn hT.le (M s) 0 (U 0)
  let Z := affineInitialValue J hc hd hi hn hT.le (M s) 0 (U 0)
  have hZ := affineInitialValue_solution J hc hd hi hn hT.le (M s) hs 0 (U 0)
  have hZ0 : Z 0 = U 0 := hZ.1
  have hZe : ∀ r ∈ Icc 0 T, J.adjoint (Z r) = J.adjoint (Z 0) +
      ∫ q in (0 : ℝ)..r, M s z q - z q + J.adjoint (J (z q)) := by
    intro r hr
    rw [hZ0]
    simpa only [add_zero] using hZ.2.2.2 r hr
  have hWe : ∀ r ∈ Icc 0 T, J.adjoint (U (s * r)) = J.adjoint (U (s * 0)) +
      ∫ q in (0 : ℝ)..r, M s w q - w q + J.adjoint (J (w q)) := by
    simpa only [mul_zero] using hWi
  have hunique := unforced_integral_heat_unique J hc hd hi hn hT (M s) hs w z
    (fun r => U (s * r)) Z hWc hZ.2.1 (by rw [mul_zero, hZ0]) hWg hZ.2.2.1 hWe hZe
  exact hunique.2 t ht

theorem contDiffAt_weak_value_of_dilation
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {a b T B : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b) (hT : 0 < T)
    (hBT : b * T ≤ B) (hB : 0 < B)
    (A : ℝ → V →L[ℝ] V) (hA : ContDiffOn ℝ ∞ A (Icc 0 B))
    (hsmall : ‖(formWeakHeatOperator J hc hd hi hn hT.le).comp
      (normalizedDilationLp J ha.le (ha1.trans h1b).le hT.le hBT hB A hA 1)‖ < 1)
    (v : ℝ → V) (hv : MemLp v 2 (timeMeasure B)) (U : ℝ → H)
    (hU : ContinuousOn U (Icc 0 B))
    (hgraph : ∀ᵐ t ∂timeMeasure B, J (v t) = U t)
    (heq : ∀ t ∈ Icc 0 B, J.adjoint (U t) = J.adjoint (U 0) +
      ∫ r in (0 : ℝ)..t, A r (v r)) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    ContDiffAt ℝ ∞ U t := by
  have hh := contDiffAt_weak_time_dilation J hc hd hi hn ha ha1 h1b hT hBT hB A hA hsmall
    v hv U hU hgraph heq (Ioc_subset_Icc_self ht)
  have hh' : ContDiffAt ℝ ∞ (fun s => U (s * t)) (t / t) := by
    simpa only [div_self ht.1.ne'] using hh
  have hlin : ContDiffAt ℝ ∞ (fun r : ℝ => r / t) t := contDiffAt_id.div_const t
  have hcomp := hh'.comp (f := fun r : ℝ => r / t) t hlin
  simpa only [Function.comp_def, div_mul_cancel₀ _ ht.1.ne'] using hcomp

end PoincareConjecture.M35.Uniqueness.Heat
