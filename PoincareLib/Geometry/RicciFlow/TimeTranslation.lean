import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-!
# Affine time translation of Ricci flows

The local Shi estimate in the M04 interface is stated for a flow on
`Set.Icc 0 T`.  This file supplies the elementary adapter which moves an
arbitrary interval subset back to that normal form while retaining the same
spatial metric and connection representatives.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlow

open Set

/-- Translate a Ricci flow by the affine time map `t ↦ t + s`.

The hypotheses only ask that the translated interval lies in the original
domain; no endpoint regularity or extension of the flow is introduced.
-/
def translate
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J K : Set ℝ}
    (F : RicciFlow n M J) (s : ℝ) (hKJ : (fun t : ℝ ↦ t + s) '' K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) : RicciFlow n M K where
  metric := fun t ↦ F.metric (t + s)
  connection := fun t ↦ F.connection (t + s)
  interval := hK
  nontrivial := hne
  smooth := by
    apply F.smooth.comp ((contMDiffOn_fst.add contMDiffOn_const).prodMk
      contMDiffOn_snd)
    intro p hp
    exact ⟨hKJ ⟨p.1, hp.1, rfl⟩, hp.2⟩
  equation := by
    intro t ht x u v
    have hmap : Set.MapsTo (fun z : ℝ ↦ z + s) K J := by
      intro z hz
      exact hKJ ⟨z, hz, rfl⟩
    have houter := F.equation (t + s) (hmap ht) x u v
    have hinner : HasDerivWithinAt (fun z : ℝ ↦ z + s) 1 K t := by
      simpa only [id_eq] using (hasDerivAt_id t).add_const s |>.hasDerivWithinAt
    have hcomp := houter.comp t hinner hmap
    simpa only [Function.comp_def, mul_one] using hcomp

theorem translate_metric
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J K : Set ℝ}
    (F : RicciFlow n M J) (s : ℝ) (hKJ : (fun t : ℝ ↦ t + s) '' K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) (t : ℝ) :
    (F.translate s hKJ hK hne).metric t = F.metric (t + s) := rfl

theorem translate_connection
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J K : Set ℝ}
    (F : RicciFlow n M J) (s : ℝ) (hKJ : (fun t : ℝ ↦ t + s) '' K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) (t : ℝ) :
    (F.translate s hKJ hK hne).connection t = F.connection (t + s) := rfl

end PoincareMT.RicciFlow
