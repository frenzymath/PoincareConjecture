import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.SlabDensity
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SurfaceSoliton

theorem measureReal_open_slab_of_closed_slabs
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} {a b c : ℝ} (hab : a < b)
    (hslab : ∀ s t : ℝ, a < s → t < b → s ≤ t →
      μ.real (f ⁻¹' Icc s t) = c * (t - s)) :
    μ.real (f ⁻¹' Ioo a b) = c * (b - a) := by
  obtain ⟨u, v, hu, hv, hua, hvb, huv, hlimu, hlimv⟩ :=
    exists_seq_strictAnti_strictMono_tendsto hab
  have hmono : Monotone (fun n => f ⁻¹' Icc (u n) (v n)) := by
    intro n m hnm x hx
    exact ⟨(hu.antitone hnm).trans hx.1, hx.2.trans (hv.monotone hnm)⟩
  have hUnion : (⋃ n, f ⁻¹' Icc (u n) (v n)) = f ⁻¹' Ioo a b := by
    ext x
    simp only [mem_iUnion, mem_preimage, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨n, hnx, hxn⟩
      exact ⟨(hua n).1.trans_le hnx, hxn.trans_lt (hvb n).2⟩
    · rintro ⟨hax, hxb⟩
      obtain ⟨n, hn⟩ := ((hlimu.eventually (gt_mem_nhds hax)).and
        (hlimv.eventually (lt_mem_nhds hxb))).exists
      exact ⟨n, hn.1.le, hn.2.le⟩
  have hleft := (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp
    (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  rw [hUnion] at hleft
  have hright := (hlimv.sub hlimu).const_mul c
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall fun n =>
    (hslab (u n) (v n) (hua n).1 (hvb n).2 (huv n n).le).symm)

end PoincareConjecture.SurfaceSoliton

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem volume_open_slab_eq_of_constant_slab_density (g : RiemannianMetric 2 M)
    {f : M → ℝ} {a b c : ℝ}
    (hslab : ∀ s t : ℝ, a < s → t < b → s ≤ t →
      ∀ H : ℝ → ℝ, Continuous H →
        (∫ x in f ⁻¹' Icc s t, H (f x) ∂g.volumeMeasure) =
          c * ∫ u in Icc s t, H u)
    {t : ℝ} (hat : a < t) (htb : t ≤ b) :
    g.volumeMeasure.real (f ⁻¹' Ioo a t) = c * (t - a) := by
  apply SurfaceSoliton.measureReal_open_slab_of_closed_slabs hat
  intro s u has hut hsu
  have h := hslab s u has (hut.trans_le htb) hsu (fun _ => 1) continuous_const
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hsu)] using h

end PoincareConjecture.RiemannianMetric
