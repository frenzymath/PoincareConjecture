import PoincareConjecture.Proofs.M47.BlowupControlsCapEnergyAt
import PoincareConjecture.Proofs.M47.BlowupControlsCapCoefficients
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance capClosedCoefficientNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capClosedCoefficientSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace



theorem exists_closed_cap_comparison_of_continuation
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    (S : MaximalStandardCapFlow F.standard_initial)
    {t : ℝ} {hbirth : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hbirth).cap_count} {A eta c d : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hcd : c < d) (hc1 : c < 1)
    {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 c) U)
    (e' : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) (Ico 0 d) U)
    (initial : SurgeryCapInitialComparison F t hbirth i A)
    (same : ∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
      e'.forward s hs' x = e.forward s hs x)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart) :
    ∃ closed : SurgeryFlowCylinder F (F.slice t) t
        ((F.parameters.h t)⁻¹ ^ 2) (Icc 0 c) U,
      (∀ s (hs : s ∈ Icc 0 c) (hs' : s ∈ Ico 0 d) x,
        closed.forward s hs x = e'.forward s hs' x) ∧
      SurgeryCapFamilyComparison F S A eta closed initial.chart := by
  rcases comparison with ⟨bound, hbound, hlifetime, _htime, himage, herror⟩
  let q := capInitialPartialDiffeomorph initial
  have htarget : q.target = U := himage
  have hmap : q.target ⊆ U := le_of_eq htarget
  have hU : IsOpen U := htarget ▸ q.open_target
  obtain ⟨G⟩ := M44.exists_cylinderRicciFlow P hpinch e' hU (hc.trans hcd) q hmap
  have hzero : (0 : E) ∈ q.source := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  let p : (⟨q.target, q.open_target⟩ : Opens (F.slice t).carrier) :=
    ⟨q 0, q.map_source hzero⟩
  let chart := M44.targetChart q p
  let B : ℝ × E → Bilin := fun z => (G.flow.metric z.1).pullbackCoefficients chart z.2
  let energy : ℝ → E → ℝ := fun s x => singularMetricJetErrorSquared
    (S.metric s) (S.connection s) (fun y v => B (s, y) (v 0) (v 1)) ⌊eta⁻¹⌋₊ x
  have old_bound (s : ℝ) (hs : s ∈ Ico 0 c) (x : E)
      (hx : x ∈ F.standard_initial.metric.ball 0 A) : energy s x ≤ bound := by
    have hs' : s ∈ Ico 0 d := ⟨hs.1, hs.2.trans hcd⟩
    have hforward : e'.forward s hs' = e.forward s hs := funext (same s hs hs')
    have hread := G.metricJetError_eq_cylinder hmap p s hs' hx
      (S.metric s) (S.connection s) ⌊eta⁻¹⌋₊
    change energy s x = singularMetricJetErrorSquared (S.metric s) (S.connection s)
      (fun y v => e'.pullbackInner s hs' (initial.chart y)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) initial.chart y (v 1))) ⌊eta⁻¹⌋₊ x at hread
    rw [hread]
    have hinner : e'.pullbackInner s hs' = e.pullbackInner s hs := by
      funext y v w
      unfold SurgeryFlowCylinder.pullbackInner
      rw [hforward]
    rw [hinner]
    exact herror s hs x hx
  have end_bound (x : E) (hx : x ∈ F.standard_initial.metric.ball 0 A) :
      energy c x ≤ bound := by
    have hcont : ContinuousAt (fun s => energy s x) c :=
      cap_moving_comparison_continuous_at S G.flow hc hcd (by rwa [hlifetime])
        q.open_source chart (M44.contMDiffOn_targetChart q p) ⌊eta⁻¹⌋₊ hx
    apply le_of_tendsto (x := 𝓝[<] c) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT hc] with s hs
    exact old_bound s ⟨hs.1.le, hs.2⟩ x hx
  have hclosed : Icc 0 c ⊆ Ico 0 d := fun _ hs => ⟨hs.1, hs.2.trans_lt hcd⟩
  let closed := e'.restrict hclosed ordConnected_Icc (Subset.rfl : U ⊆ U)
  refine ⟨closed, fun _ _ _ _ => rfl, ?_⟩
  apply M44.surgeryCapFamilyComparison_of_coefficient_error S closed initial.chart
    q.open_source (Subset.rfl : F.standard_initial.metric.ball 0 A ⊆ q.source)
    B bound hbound hlifetime
  · intro s hs
    rw [hlifetime]
    exact ⟨hs.1, hs.2.trans_lt hc1⟩
  · exact himage
  · intro s hs y hy v w
    exact G.pullback_eq_cylinder hmap p s (hclosed hs) hy v w
  · intro s hs x hx
    change energy s x ≤ bound
    rcases hs.2.eq_or_lt with hsc | hsc
    · subst s
      exact end_bound x hx
    · exact old_bound s ⟨hs.1, hsc⟩ x hx

end PoincareConjecture.M47
