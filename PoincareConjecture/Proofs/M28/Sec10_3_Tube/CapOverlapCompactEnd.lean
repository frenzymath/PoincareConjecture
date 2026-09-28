import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderEndRegions
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutExhaustion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapTubeAttachment

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  {X : Set M} {cap : CapCertificate g} {tube : EpsilonTubeCertificate g X}
  {side : Bool}

theorem exists_compact_overlap_end (A : CapTubeAttachment cap tube side) :
    ∃ q : ℝ, 0 < q ∧ q < cap.epsilon⁻¹ ∧
      IsCompact (closure (cap.closed_core ∪
        cap.end_neck.region (-cap.epsilon⁻¹) q)) ∧
      closure (cap.closed_core ∪ cap.end_neck.region (-cap.epsilon⁻¹) q) ⊆
        cap.carrier ∧
      ∃ overlapSide : Bool, A.overlap_model.tail overlapSide (1 / 2) ⊆
        closure (cap.closed_core ∪ cap.end_neck.region (-cap.epsilon⁻¹) q) := by
  let E := A.overlap_model
  obtain ⟨q₀, hq₀, hq₀L, hmiddle⟩ := cap.exists_recut_capturing_compact
    E.isCompact_middleSphere (E.middleSphere_subset.trans inter_subset_left)
  obtain ⟨s, hs, htail⟩ := A.cap_tail
  obtain ⟨q, hqmax, hqL⟩ := exists_between (max_lt hq₀L hs.2)
  have hq₀q : q₀ < q := (le_max_left _ _).trans_lt hqmax
  have hsq : s < q := (le_max_right _ _).trans_lt hqmax
  have hq : 0 < q := hq₀.trans hq₀q
  obtain ⟨q', hqq', hq'L⟩ := exists_between hqL
  have hq' : 0 < q' := hq.trans hqq'
  have hL : 0 < cap.epsilon⁻¹ := inv_pos.mpr cap.epsilon_pos
  let Outer := cap.end_neck.region q cap.epsilon⁻¹
  have hOuter : Outer ⊆ cap.carrier ∩ tube.carrier := by
    intro x hx
    exact ⟨cap.end_neck_subset hx.1, htail ⟨hx.1, hsq.trans hx.2.1, hx.2.2⟩⟩
  have hconn : IsPreconnected Outer := cap.end_neck.isPreconnected_region
    (by rw [cap.end_neck_epsilon]; linarith)
    (by rw [cap.end_neck_epsilon])
  have hcontinuous : ContinuousOn (fun x => (E.inverse x).2) Outer :=
    (continuous_snd.comp_continuousOn E.inverse_smooth.continuousOn).mono hOuter
  have hneq : ∀ x ∈ Outer, (E.inverse x).2 ≠ 1 / 2 := by
    intro x hx heq
    have hxmiddle := (E.mem_middleSphere_iff (hOuter hx)).mpr heq
    rcases hmiddle hxmiddle with hxcore | hxinner
    · rw [cap.closed_core_eq_complement_end] at hxcore
      exact hxcore.2 hx.1
    · linarith [hxinner.2.2, hx.2.1]
  let W := cap.closed_core ∪ cap.end_neck.region (-cap.epsilon⁻¹) q'
  obtain ⟨_, hWcompact, hWcap⟩ := cap.open_precompact_recut
    ((neg_neg_of_pos hL).trans hq') hq'L
  have houtside {x : M} (hx : x ∈ cap.carrier ∩ tube.carrier)
      (hxW : x ∉ W) : x ∈ Outer := by
    have hxend : x ∈ cap.end_neck.carrier := by
      by_contra h
      apply hxW
      apply Or.inl
      rw [cap.closed_core_eq_complement_end]
      exact ⟨hx.1, h⟩
    have hlo : -cap.epsilon⁻¹ < (cap.end_neck.coordinate_inverse x).2 := by
      simpa only [cap.end_neck_epsilon] using
        (cap.end_neck.coordinate_inverse_mem x hxend).2.1
    have hhi : (cap.end_neck.coordinate_inverse x).2 < cap.epsilon⁻¹ := by
      simpa only [cap.end_neck_epsilon] using
        (cap.end_neck.coordinate_inverse_mem x hxend).2.2
    have hq'x : q' ≤ (cap.end_neck.coordinate_inverse x).2 := by
      by_contra h
      exact hxW (Or.inr ⟨hxend, hlo, lt_of_not_ge h⟩)
    exact ⟨hxend, hqq'.trans_le hq'x, hhi⟩
  refine ⟨q', hq', hq'L, hWcompact, hWcap, ?_⟩
  rcases hconn.mapsTo_Ioi_or_Iio hcontinuous hneq with hhigh | hlow
  · refine ⟨false, ?_⟩
    intro x hx
    have hx' := (E.mem_tail_iff_m28 false (by norm_num) (by norm_num)).mp hx
    by_cases hxW : x ∈ W
    · exact subset_closure hxW
    · exact False.elim ((not_lt_of_ge (hhigh (houtside hx'.1 hxW)).le) hx'.2)
  · refine ⟨true, ?_⟩
    intro x hx
    have hx' := (E.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mp hx
    by_cases hxW : x ∈ W
    · exact subset_closure hxW
    · exact False.elim ((not_lt_of_ge hx'.2.le) (hlow (houtside hx'.1 hxW)))

end PoincareConjecture.CapTubeAttachment
