import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

theorem cylinder_preterminal_mem_regular_limit
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale)) {x : C.carrier} (hx : x ∈ U)
    (hbound : ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K) :
    ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        (F.event (origin + c / scale) hT).regular_limit := by
  let event := F.event (origin + c / scale) hT
  rw [event.regular_limit_eq]
  obtain ⟨K, hK⟩ := hbound
  refine ⟨K, ?_⟩
  intro t0 ht0
  have hlower : scale * (t0 - origin) < c := by
    have ht : t0 - origin < c / scale := by linarith
    simpa only [mul_comm] using (lt_div_iff₀ e.scale_pos).mp ht
  obtain ⟨s, hs0, hsc⟩ := exists_between (max_lt hr.2 hlower)
  have hrs : r < s := (le_max_left _ _).trans_lt hs0
  have hs : s ∈ Ico (0 : ℝ) c := ⟨hr.1.trans hrs.le, hsc⟩
  have hs' : origin + s / scale ∈ Ico event.tMinus (origin + c / scale) := by
    refine ⟨hr'.1.trans ?_, ?_⟩
    · linarith [(div_le_div_iff_of_pos_right e.scale_pos).mpr hrs.le]
    · linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hsc]
  have ht0s : t0 < origin + s / scale := by
    have hmul := (le_max_right _ _).trans_lt hs0
    have hdiv : t0 - origin < s / scale :=
      (lt_div_iff₀ e.scale_pos).mpr (by simpa only [mul_comm] using hmul)
    linarith
  refine ⟨origin + s / scale, hs', ht0s, ?_⟩
  have hp := cylinder_preterminal_coordinates_eq_of_pinched P hpinch e hT
    s hs r hr hs' hr' x hx
  let y := (event.pre_identify ⟨origin + s / scale, hs'⟩).symm (e.forward s hs x)
  have hhom : MetricHomothety (event.pre_flow.metric (origin + s / scale))
      (F.metric (origin + s / scale)) (event.pre_identify ⟨origin + s / scale, hs'⟩) 1 := by
    intro z v w
    simpa only [one_mul] using event.pre_metric ⟨origin + s / scale, hs'⟩ z v w
  have heq := M13.homothety_scalarCurvature_eq _ _ _ 1 zero_lt_one hhom
    (event.pre_flow.connection (origin + s / scale)) (F.connection (origin + s / scale)) y
  dsimp only [y] at heq
  rw [Diffeomorph.apply_symm_apply, div_one, hp] at heq
  exact heq.symm.trans_le (hK s hs)

noncomputable def cylinderTerminalChart
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale)) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      (F.event (origin + c / scale) hT).terminal.carrier ∞ :=
  ((cylinderSliceChart e hU r hr).trans
    ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm.toPartialDiffeomorph).trans
      (regionEquivalenceInteriorChart (F.event (origin + c / scale) hT).limit_identify)

theorem cylinderTerminalChart_source
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U) (hU : IsOpen U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈ Ico (F.event (origin + c / scale) hT).tMinus
      (origin + c / scale))
    (hbound : ∀ x ∈ U, ∃ K : ℝ, ∀ s (hs : s ∈ Ico (0 : ℝ) c),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K) :
    (cylinderTerminalChart e hU hT r hr hr').source = U := by
  ext x
  change ((x ∈ U ∧ e.forward r hr x ∈
    (univ : Set (F.slice (origin + r / scale)).carrier)) ∧
    ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).regular_limit) ↔ x ∈ U
  rw [(F.event (origin + c / scale) hT).regular_limit_open.interior_eq]
  exact ⟨fun hx => hx.1.1, fun hx => ⟨⟨hx, mem_univ _⟩,
    cylinder_preterminal_mem_regular_limit P hpinch e hT r hr hr' hx (hbound x hx)⟩⟩

end PoincareConjecture.M44
