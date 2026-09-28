import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem continuous_scalar_timeSubtype (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) :
    Continuous (fun z : J × M => (F.connection z.1.val).scalarCurvature z.2) := by
  have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have h := (hC.scalar_regular 3 M J F).continuousOn.comp_continuous hmap
    (fun z => ⟨z.1.property, mem_univ z.2⟩)
  exact h



theorem scalar_uniform_near_time_on_compact (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {K : Set M} (hK : IsCompact K)
    (t : J) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ s : J in 𝓝 t, ∀ x ∈ K,
      |(F.connection s.val).scalarCurvature x -
        (F.connection t.val).scalarCurvature x| < eta := by
  have hf := continuous_scalar_timeSubtype hC F
  have hbase := hf.comp (continuous_const.prodMk continuous_snd :
    Continuous (fun z : J × M => (t, z.2)))
  have hdiff := (hf.sub hbase).abs
  apply hK.eventually_forall_of_forall_eventually
  intro x _
  exact hdiff.continuousAt.eventually (Iio_mem_nhds (by
    change |(F.connection t.val).scalarCurvature x -
      (F.connection t.val).scalarCurvature x| < eta
    simpa only [sub_self, abs_zero] using heta))



theorem continuous_scalarSup_on_compact (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {K : Set M} (hK : IsCompact K) :
    Continuous (fun t : J => scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) K) := by
  have h := hK.continuous_sSup
    (f := fun (t : J) x => (F.connection t.val).scalarCurvature x)
    (continuous_scalar_timeSubtype hC F)
  simpa only [scalarCurvatureSupOn, image_eq_range] using h



theorem continuous_scalarInf_on_compact (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {K : Set M} (hK : IsCompact K) :
    Continuous (fun t : J => sInf (range (fun x : K =>
      (F.connection t.val).scalarCurvature x.val))) := by
  have h := hK.continuous_sInf
    (f := fun (t : J) x => (F.connection t.val).scalarCurvature x)
    (continuous_scalar_timeSubtype hC F)
  simpa only [image_eq_range] using h

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem cap_uniform_scalar_lower {g : RiemannianMetric 3 M} (N : CapCertificate g) :
    ∃ m : ℝ, 0 < m ∧ ∃ b : ℝ, 1 ≤ b ∧ b < N.cap_constant ∧
      (∀ x ∈ N.carrier, m ≤ N.connection.scalarCurvature x) ∧
      ∀ x ∈ N.carrier, ∀ y ∈ N.carrier,
        N.connection.scalarCurvature y ≤ b * N.connection.scalarCurvature x := by
  obtain ⟨x0, hx0⟩ := N.core_nonempty
  have hxcarrier : x0 ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at hx0
    have hxclosed := interior_subset hx0
    rw [N.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.1
  have hR0 := N.scalar_pos x0 hxcarrier
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  have hb1 : 1 ≤ b := by
    nlinarith [hratio x0 hxcarrier x0 hxcarrier]
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  refine ⟨N.connection.scalarCurvature x0 / b, div_pos hR0 hbpos,
    b, hb1, hb, ?_, hratio⟩
  intro x hx
  exact (div_le_iff₀ hbpos).mpr (by
    simpa only [mul_comm] using hratio x hx x0 hxcarrier)




theorem cap_scalar_ratio_persists [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J)
    (t : J) (N : CapCertificate (F.metric t.val))
    (hconnection : N.connection = F.connection t.val) :
    ∃ b' : ℝ, b' < N.cap_constant ∧
      ∀ᶠ s : J in 𝓝 t,
        (∀ x ∈ N.carrier, 0 < (F.connection s.val).scalarCurvature x) ∧
        ∀ x ∈ N.carrier, ∀ y ∈ N.carrier,
          (F.connection s.val).scalarCurvature y ≤
            b' * (F.connection s.val).scalarCurvature x := by
  obtain ⟨m, hm, b, hb1, hbC, hlower, hratio⟩ := cap_uniform_scalar_lower N
  rw [hconnection] at hlower hratio
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hd : 0 < N.cap_constant - b := sub_pos.mpr hbC
  let eta := min (m / 2) ((N.cap_constant - b) * m / (4 * (b + 1)))
  have heta : 0 < eta :=
    lt_min (half_pos hm) (div_pos (mul_pos hd hm) (by positivity))
  have hetam : eta ≤ m / 2 := min_le_left _ _
  have hetab : (b + 1) * eta ≤ (N.cap_constant - b) * m / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (b + 1))).mp
      (min_le_right (m / 2) ((N.cap_constant - b) * m / (4 * (b + 1))))
    change eta * (4 * (b + 1)) ≤ (N.cap_constant - b) * m at h
    nlinarith
  have hnear := scalar_uniform_near_time_on_compact hC F isCompact_univ t heta
  refine ⟨(N.cap_constant + b) / 2, by linarith, ?_⟩
  filter_upwards [hnear] with s hs
  have hnewlower (x : M) (hx : x ∈ N.carrier) :
      m / 2 < (F.connection s.val).scalarCurvature x := by
    have hdiff := (abs_lt.mp (hs x (mem_univ x))).1
    linarith [hlower x hx]
  refine ⟨fun x hx => (half_pos hm).trans (hnewlower x hx), ?_⟩
  intro x hx y hy
  have hdx := (abs_lt.mp (hs x (mem_univ x))).1
  have hdy := (abs_lt.mp (hs y (mem_univ y))).2
  have hmove := mul_lt_mul_of_pos_left hdx hbpos
  have hgain := mul_lt_mul_of_pos_left (hnewlower x hx) (half_pos hd)
  have hratioxy := hratio x hx y hy
  nlinarith

end PoincareConjecture.Proofs.M47
