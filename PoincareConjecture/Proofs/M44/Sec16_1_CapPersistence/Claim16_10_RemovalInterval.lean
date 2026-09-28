import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_InitialCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_MaximalCylinder

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

def restrictCylinderInterval
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I J : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U) (hJI : J ⊆ I)
    (hJ : OrdConnected J) : SurgeryFlowCylinder F C origin scale J U where
  scale_pos := e.scale_pos
  interval_connected := hJ
  time_subset := (image_mono hJI).trans e.time_subset
  forward s hs := e.forward s (hJI hs)
  inverse s hs := e.inverse s (hJI hs)
  forward_smooth s hs := e.forward_smooth s (hJI hs)
  inverse_smooth s hs := e.inverse_smooth s (hJI hs)
  left_inverse s hs := e.left_inverse s (hJI hs)
  right_inverse s hs := e.right_inverse s (hJI hs)
  slab_compatibility a b hab hK hNo s hs t ht hs' ht' :=
    e.slab_compatibility a b hab hK hNo s (hJI hs) t (hJI ht) hs' ht'
  retained_at_surgery s hs hT _ hprev :=
    e.retained_at_surgery s (hJI hs) hT (by
      obtain ⟨t, ht, hts⟩ := hprev
      exact ⟨t, hJI ht, hts⟩)
  pre_retained_at_surgery s hs hT _ t ht ht' :=
    e.pre_retained_at_surgery s (hJI hs) hT t (hJI ht) ht'
  surgery_compatibility s hs hT _ t ht ht' :=
    e.surgery_compatibility s (hJI hs) hT t (hJI ht) ht'

theorem exists_based_cylinder_of_duration_le
    {F : SurgeryFlowData.{u}} {origin scale b c : ℝ}
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x) (hbc : b ≤ c) :
    ∃ e' : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 b) U,
      ∀ h x, x ∈ U → HEq (e'.forward 0 h x) x := by
  let e' := restrictCylinderInterval e (Ico_subset_Ico_right hbc) ordConnected_Ico
  exact ⟨e', fun h x hx => hinitial _ x hx⟩

theorem exists_based_cylinder_of_maximal_duration_bound
    (F : SurgeryFlowData.{u}) {origin scale b B : ℝ}
    (hscale : 0 < scale) (hB : 0 < B)
    (htime : ∀ s ∈ Ico 0 B, origin + s / scale ∈ F.time_domain)
    (U : Set (F.slice origin).carrier)
    (hbound : ∀ c : ℝ, 0 < c → c ≤ B →
      ∀ e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U,
      (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) →
      (∀ d : ℝ, c < d → d ≤ B →
        ¬ ∃ e' : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) U,
          ∀ h x, x ∈ U → HEq (e'.forward 0 h x) x) → b ≤ c) :
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 b) U,
      ∀ h x, x ∈ U → HEq (e.forward 0 h x) x := by
  obtain ⟨c0, hc0, hc0B, e0, hinitial0⟩ := exists_initial_based_cylinder F hscale hB htime U
  obtain ⟨c, hc, hcB, e, hinitial, _hagree, hstop⟩ :=
    exists_maximal_based_cylinder e0 hc0 hc0B.le hinitial0
  exact exists_based_cylinder_of_duration_le e hinitial (hbound c hc hcB e hinitial hstop)

end PoincareConjecture.M44
