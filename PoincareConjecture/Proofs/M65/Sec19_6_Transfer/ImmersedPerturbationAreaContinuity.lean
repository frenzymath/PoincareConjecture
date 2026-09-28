import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.FillingLimit
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FlowFillingScaling
import PoincareConjecture.Proofs.M62.Cor0_3_AmbientBounds

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b circumference : ℝ} {J : Set ℝ} {F : RicciFlow 3 M (Icc a b)}

theorem fillingArea_continuousOn (P : M62.CircleProductData F circumference)
    (hJF : J ⊆ Icc a b) (disks : ∀ q ∈ J, M64DiskAreaComparison P q)
    (loops : ℝ → C1FreeLoopSpace (M := M)) (hloops : ContinuousOn loops J)
    (hfilled : ∀ q ∈ J, Nonempty (LipschitzSpanningDisk (F.metric q) (loops q))) :
    ContinuousOn (fun q => fillingArea (F.metric q) (loops q)) J := by
  obtain ⟨K0, K1, K2, _, bounds⟩ := M62.exists_ambient_bounds F isCompact_univ
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_iff_seqContinuous.mpr
  intro seq q hseq
  change Tendsto (fun n => fillingArea (F.metric (seq n)) (loops (seq n))) atTop
    (𝓝 (fillingArea (F.metric q) (loops q)))
  have hreal : Tendsto (fun n => (seq n : ℝ)) atTop (𝓝 (q : ℝ)) :=
    (continuous_subtype_val.tendsto q).comp hseq
  have hloop : Tendsto (fun n => loops (seq n)) atTop (𝓝 (loops q)) :=
    ((continuousOn_iff_continuous_domRestrict.mp hloops).tendsto q).comp hseq
  have hfixed (n : ℕ) :
      Nonempty (LipschitzSpanningDisk (F.metric q) (loops (seq n))) := by
    obtain ⟨D⟩ := hfilled (seq n) (seq n).property
    exact ⟨m65TransportSpanningDisk bounds (hJF (seq n).property) (hJF q.property) D⟩
  have harea := (m65FillingArea_tendsto_of_C1 P q (disks q q.property) isCompact_univ
    (fun n => loops (seq n)) (loops q) hloop hfixed).2
  let E : ℕ → ℝ := fun n => Real.exp ((2 * K2) * |(seq n : ℝ) - q|)
  have hE : Tendsto E atTop (𝓝 1) := by
    have hzero : Tendsto (fun n => (2 * K2) * |(seq n : ℝ) - q|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero, mul_zero] using
        ((hreal.sub_const (q : ℝ)).abs).const_mul (2 * K2)
    simpa only [E, Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp hzero
  have hlower (n : ℕ) :
      fillingArea (F.metric q) (loops (seq n)) / E n ≤
        fillingArea (F.metric (seq n)) (loops (seq n)) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := m65FillingArea_flowMetric_le bounds (hJF (seq n).property)
      (hJF q.property) (loops (seq n)) (hfilled (seq n) (seq n).property)
    rw [abs_sub_comm] at h
    exact h.trans_eq (mul_comm _ _)
  have hupper (n : ℕ) :
      fillingArea (F.metric (seq n)) (loops (seq n)) ≤
        E n * fillingArea (F.metric q) (loops (seq n)) :=
    m65FillingArea_flowMetric_le bounds (hJF q.property) (hJF (seq n).property)
      (loops (seq n)) (hfixed n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [Pi.div_def, div_one] using harea.div hE one_ne_zero)
    (by simpa only [one_mul] using hE.mul harea) hlower hupper

end PoincareConjecture.M65Perturbation
