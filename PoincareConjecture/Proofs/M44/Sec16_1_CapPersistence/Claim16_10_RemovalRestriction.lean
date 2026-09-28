import PoincareConjecture.Definitions.Ch16.CapPersistence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44




def restrictCylinderSource
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U V : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U) (hVU : V ⊆ U) :
    SurgeryFlowCylinder F C origin scale I V where
  scale_pos := e.scale_pos
  interval_connected := e.interval_connected
  time_subset := e.time_subset
  forward := e.forward
  inverse := e.inverse
  forward_smooth s hs := (e.forward_smooth s hs).mono hVU
  inverse_smooth s hs := (e.inverse_smooth s hs).mono (image_mono hVU)
  left_inverse s hs _ hx := e.left_inverse s hs (hVU hx)
  right_inverse s hs _ hx := e.right_inverse s hs (image_mono hVU hx)
  slab_compatibility a b hab hJ hNo s hs t ht hs' ht' x hx :=
    e.slab_compatibility a b hab hJ hNo s hs t ht hs' ht' x (hVU hx)
  retained_at_surgery s hs hT _ hprev :=
    (image_mono hVU).trans (e.retained_at_surgery s hs hT hprev)
  pre_retained_at_surgery s hs hT _ t ht ht' x hx :=
    e.pre_retained_at_surgery s hs hT t ht ht' x (hVU hx)
  surgery_compatibility s hs hT _ t ht ht' x hx :=
    e.surgery_compatibility s hs hT t ht ht' x (hVU hx)




theorem disappears_restrict_source
    {F : SurgeryFlowData.{u}} {origin scale tPlus : ℝ} {I : Set ℝ}
    {U V : Set (F.slice origin).carrier}
    {e : SurgeryFlowCylinder F (F.slice origin) origin scale I U}
    (he : SurgeryBallDisappearsAt F e tPlus) (hVU : V ⊆ U) :
    SurgeryBallDisappearsAt F (restrictCylinderSource e hVU) tPlus := by
  rcases he with hempty | ⟨hT, hn, hinitial, s0, hs0, hlost⟩
  · exact Or.inl hempty
  · refine Or.inr ⟨hT, hn, ?_, s0, hs0, ?_⟩
    · intro h x hx
      exact hinitial h x (hVU hx)
    · intro s hs hlate x hx ht
      exact hlost s hs hlate x (hVU hx) ht

end PoincareConjecture.M44
