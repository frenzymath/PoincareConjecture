import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.SupportedChartHomeomorph

/-!
# Whole inverse formulas for an actual supported chart extension

The coordinate source is preserved by the inverse motion. The literal
chart-conjugated inverse and the entire exterior identity then follow
from injectivity of the actual ambient extension. See Hudson1969,
Lemma4.6, pp.97--99, and Dehn031, section2.
-/

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

/-- The inverse of an actual supported chart extension has its complete
chart-target formula and fixes the whole exterior of the support image.
No totalized chart inverse is used outside its target.
See Dehn031, section2 and Hudson1969, Lemma4.6. -/
theorem supported_chart_symm_eqOn {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    (Q : OpenPartialHomeomorph E X) (H : E ≃ₜ E) (F : X ≃ₜ X)
    {K : Set E} (hKS : K ⊆ Q.source) (hfix : EqOn H id Kᶜ)
    (hFQ : EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target)
    (hFout : EqOn F id (Q '' K)ᶜ) :
    EqOn F.symm (Q.symm.trans (H.symm.toOpenPartialHomeomorph.trans Q)) Q.target ∧
      EqOn F.symm id (Q '' K)ᶜ := by
  have hinvfix : EqOn H.symm id Kᶜ := by
    intro x hx
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hfix hx]
    rfl
  have hsource : MapsTo H.symm Q.source Q.source := by
    intro x hx
    by_contra hn
    have hnotK : H.symm x ∉ K := fun h => hn (hKS h)
    have he : H.symm x = x := H.symm.injective (hinvfix hnotK)
    exact hn (he.symm ▸ hx)
  constructor
  · intro y hy
    have hx : H.symm (Q.symm y) ∈ Q.source := hsource (Q.map_target hy)
    apply F.injective
    change F (F.symm y) = F (Q (H.symm (Q.symm y)))
    rw [F.apply_symm_apply, hFQ (Q.map_source hx)]
    change y = Q (H (Q.symm (Q (H.symm (Q.symm y)))))
    rw [Q.left_inv hx, H.apply_symm_apply, Q.right_inv hy]
  · intro y hy
    apply F.injective
    change F (F.symm y) = F y
    rw [F.apply_symm_apply, hFout hy]
    rfl

end OpenPartialHomeomorph
