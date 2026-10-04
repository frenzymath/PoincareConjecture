import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry

/-!
# Restricting whole-ball removal to the requested tracked ball

The positive collar sphere may require an auxiliary birth radius larger
than the requested radius. Both the actual cylinder and its disappearance
restrict to every smaller source region. Morgan--Tian, Claim 16.10 and
Proposition 16.5, pp. 374-375; M44 derivation 79.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M44

/-- Restrict the original physical transport maps to a smaller
tracked birth region. Source: Proposition 16.5, pp. 374-375;
M44 derivation 79. -/
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

/-- Whole-region disappearance passes to the restricted physical
cylinder without changing its times or transport maps. Source:
Claim 16.10, p. 375; M44 derivation 79. -/
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

end PoincareMT.M44
