import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderClock
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.SpliceTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {b : F.box_index}
  {a q : ℝ} {I : Set ℝ} {U : Set (F.box b).carrier.carrier}
  (e : GeneralizedFlowCylinder F (F.box b).carrier a q I U)
  {T Q base cut : ℝ} (hQ : 0 < Q) (hbase : base < cut)
  (hbox : Ioc base T ⊆ (F.box b).interval)
  (hold : ∀ s ∈ Ioc (-1 : ℝ) 0, T + s / Q ≤ cut → (T + s / Q - a) * q ∈ I)

include hQ in
private theorem newClock_le {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0) : T + s / Q ≤ T := by
  have h := div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
  linarith

def spliceForward (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
    (F.box b).carrier.carrier → (F.slice (T + s / Q)).carrier := by
  classical
  exact if hc : T + s / Q ≤ cut then e.forwardAtTime (T + s / Q) (hold s hs hc)
    else (F.box b).forward (T + s / Q)
      (hbox ⟨hbase.trans (lt_of_not_ge hc), newClock_le hQ hs⟩)

def spliceInverse (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
    (F.slice (T + s / Q)).carrier → (F.box b).carrier.carrier := by
  classical
  exact if hc : T + s / Q ≤ cut then e.inverseAtTime (T + s / Q) (hold s hs hc)
    else (F.box b).inverse (T + s / Q)
      (hbox ⟨hbase.trans (lt_of_not_ge hc), newClock_le hQ hs⟩)

theorem spliceForward_early (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hc : T + s / Q ≤ cut) :
    e.spliceForward hQ hbase hbox hold s hs = e.forwardAtTime (T + s / Q) (hold s hs hc) := by
  simp only [spliceForward, dif_pos hc]

variable (hoverlap : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
  (hl : base < T + s / Q) (hc : T + s / Q ≤ cut) (x : (F.box b).carrier.carrier), x ∈ U →
    e.forwardAtTime (T + s / Q) (hold s hs hc) x =
      (F.box b).forward (T + s / Q) (hbox ⟨hl, newClock_le hQ hs⟩) x)

include hoverlap

theorem spliceForward_late (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hl : base < T + s / Q) (x : (F.box b).carrier.carrier) (hx : x ∈ U) :
    e.spliceForward hQ hbase hbox hold s hs x =
      (F.box b).forward (T + s / Q) (hbox ⟨hl, newClock_le hQ hs⟩) x := by
  classical
  unfold spliceForward
  split_ifs with hc
  · exact hoverlap s hs hl hc x hx
  · rfl

theorem spliceForward_embedding :
    Topology.IsEmbedding (fun p : Ioc (-1 : ℝ) 0 × U =>
      (⟨T + p.1.1 / Q, e.spliceForward hQ hbase hbox hold p.1 p.1.property p.2⟩ : F.point)) := by
  let clock : ℝ ≃ₜ ℝ := (Homeomorph.mulRight₀ Q⁻¹ (inv_ne_zero hQ.ne')).trans
    (Homeomorph.addLeft T)
  let X := Ioc (-1 : ℝ) 0 × U
  let time : X → ℝ := fun p => T + p.1.1 / Q
  let f : X → F.point := fun p =>
    ⟨time p, e.spliceForward hQ hbase hbox hold p.1 p.1.property p.2⟩
  have htime : Continuous time := continuous_const.add
    ((continuous_subtype_val.comp continuous_fst).div_const Q)
  have hparam : Topology.IsEmbedding (fun p : X => (time p, p.2)) := by
    exact (clock.isEmbedding.prodMap Topology.IsEmbedding.id).comp
      (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id)
  apply SingularRegularLimit.isEmbedding_of_time_regions htime F.time_continuous
    (fun _ => rfl) hbase
  · let embed : {p : X | time p < cut} → {t : ℝ | (t - a) * q ∈ I} × U := fun p =>
      (⟨time p.1, hold p.1.1 p.1.1.property p.property.le⟩, p.1.2)
    have hembed : Topology.IsEmbedding embed := by
      apply (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).of_comp_iff.mp
      exact hparam.comp Topology.IsEmbedding.subtypeVal
    have heq : (fun p : {p : X | time p < cut} => f p) =
        (fun p : {t : ℝ | (t - a) * q ∈ I} × U =>
          (⟨p.1, e.forwardAtTime p.1 p.1.property p.2⟩ : F.point)) ∘ embed := by
      funext p
      apply congrArg (Sigma.mk (time p.1))
      exact congrFun (e.spliceForward_early hQ hbase hbox hold p.1.1 p.1.1.property p.property.le) _
    change Topology.IsEmbedding (fun p : {p : X | time p < cut} => f p)
    rw [heq]
    exact e.forwardAtTime_embedding.comp hembed
  · let embed : {p : X | base < time p} → (F.box b).interval × (F.box b).carrier.carrier :=
      fun p => (⟨time p.1, hbox ⟨p.property, newClock_le hQ p.1.1.property⟩⟩, p.1.2)
    have hembed : Topology.IsEmbedding embed := by
      apply (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).of_comp_iff.mp
      exact ((clock.isEmbedding.prodMap Topology.IsEmbedding.subtypeVal).comp
        (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id)).comp
        Topology.IsEmbedding.subtypeVal
    have heq : (fun p : {p : X | base < time p} => f p) =
        (fun p : (F.box b).interval × (F.box b).carrier.carrier =>
          (⟨p.1, (F.box b).forward p.1 p.1.property p.2⟩ : F.point)) ∘ embed := by
      funext p
      apply congrArg (Sigma.mk (time p.1))
      exact e.spliceForward_late hQ hbase hbox hold hoverlap p.1.1 p.1.1.property
        p.property p.1.2 p.1.2.property
    change Topology.IsEmbedding (fun p : {p : X | base < time p} => f p)
    rw [heq]
    exact (F.box_openEmbedding b).isEmbedding.comp hembed

theorem spliceForward_vertical_compatibility (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (x : (F.box b).carrier.carrier) (hx : x ∈ U) :
    ∃ c, ∃ y : (F.box c).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' hs', |s' - s| < δ → ∃ hc : T + s' / Q ∈ (F.box c).interval,
        e.spliceForward hQ hbase hbox hold s' hs' x = (F.box c).forward (T + s' / Q) hc y := by
  by_cases hl : base < T + s / Q
  · refine ⟨b, x, (T + s / Q - base) * Q, mul_pos (sub_pos.mpr hl) hQ, ?_⟩
    intro s' hs' hdist
    have hphysical : |(T + s' / Q) - (T + s / Q)| < T + s / Q - base := by
      rw [show (T + s' / Q) - (T + s / Q) = (s' - s) / Q by ring,
        abs_div, abs_of_pos hQ]
      exact (div_lt_iff₀ hQ).mpr hdist
    have hlate : base < T + s' / Q := by
      have h := (abs_lt.mp hphysical).1
      linarith
    exact ⟨hbox ⟨hlate, newClock_le hQ hs'⟩,
      e.spliceForward_late hQ hbase hbox hold hoverlap s' hs' hlate x hx⟩
  · have hearly : T + s / Q < cut := (le_of_not_gt hl).trans_lt hbase
    obtain ⟨c, y, δ, hδ, hloc⟩ :=
      e.forwardAtTime_vertical_compatibility (T + s / Q) (hold s hs hearly.le) x hx
    refine ⟨c, y, min (δ * Q) ((cut - (T + s / Q)) * Q),
      lt_min (mul_pos hδ hQ) (mul_pos (sub_pos.mpr hearly) hQ), ?_⟩
    intro s' hs' hdist
    have hphysical : |(T + s' / Q) - (T + s / Q)| < min δ (cut - (T + s / Q)) := by
      rw [show (T + s' / Q) - (T + s / Q) = (s' - s) / Q by ring,
        abs_div, abs_of_pos hQ]
      apply lt_min
      · exact (div_lt_iff₀ hQ).mpr (hdist.trans_le (min_le_left _ _))
      · exact (div_lt_iff₀ hQ).mpr (hdist.trans_le (min_le_right _ _))
    have hcut : T + s' / Q ≤ cut := by
      have h := (abs_lt.mp (hphysical.trans_le (min_le_right _ _))).2
      linarith
    obtain ⟨hc, heq⟩ := hloc (T + s' / Q) (hold s' hs' hcut)
      (hphysical.trans_le (min_le_left _ _))
    refine ⟨hc, ?_⟩
    rw [e.spliceForward_early hQ hbase hbox hold s' hs' hcut]
    exact heq



def spliceBox : GeneralizedFlowCylinder F (F.box b).carrier T Q (Ioc (-1) 0) U := by
  classical
  refine {
    scale_pos := hQ
    forward := e.spliceForward hQ hbase hbox hold
    inverse := e.spliceInverse hQ hbase hbox hold
    forward_smooth := ?_
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := e.spliceForward_embedding hQ hbase hbox hold hoverlap
    vertical_compatibility := e.spliceForward_vertical_compatibility hQ hbase hbox hold hoverlap }
  · intro s hs
    unfold spliceForward
    split_ifs
    · exact e.forwardAtTime_smooth _ _
    · exact ((F.box b).forward_smooth _ _).contMDiffOn
  · intro s hs
    unfold spliceForward spliceInverse
    split_ifs
    · exact e.inverseAtTime_smooth _ _
    · exact ((F.box b).inverse_smooth _ _).mono (image_subset_range _ _)
  · intro s hs x hx
    unfold spliceForward spliceInverse
    split_ifs
    · exact e.inverseAtTime_forwardAtTime _ _ hx
    · exact (F.box b).left_inverse _ _ x
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    unfold spliceForward spliceInverse
    split_ifs
    · rw [e.inverseAtTime_forwardAtTime _ _ hx]
    · rw [(F.box b).left_inverse]

end PoincareConjecture.GeneralizedFlowCylinder
