import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.GeometricGraphComponents

/-!
# Geometric intersections controlled by graph supports

Injective vertex realization and simplicial edge incidence turn
a common-support bound into the same geometric carrier bound.
See Alexander 1924, p. 6 and M76 derivation 149.
-/

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Adding graph edges enlarges the realized segment carrier.
See Alexander p. 6 and M76 derivation 149. -/
theorem segmentCarrier_mono {G H : SimpleGraph V} (hGH : G ≤ H) (p : V → E) :
    G.segmentCarrier p ⊆ H.segmentCarrier p := by
  rintro x ⟨v, w, hvw, hx⟩
  exact ⟨v, w, hGH hvw, hx⟩

/-- Two subgraphs whose supports meet only at one vertex have
realized segment carriers meeting only at its image, provided
the original geometric edges satisfy simplicial incidence.
See Alexander p. 6 and M76 derivation 149. -/
theorem segmentCarrier_inter_subset_of_support_inter (G H J : SimpleGraph V)
    (hHG : H ≤ G) (hJG : J ≤ G) (p : V → E) (q : V)
    (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b}))
    (hsupport : H.support ∩ J.support ⊆ {q}) :
    H.segmentCarrier p ∩ J.segmentCarrier p ⊆ {p q} := by
  rintro x ⟨⟨v, w, hvw, hx⟩, ⟨a, b, hab, hy⟩⟩
  have hleft : ({p v, p w} : Set E) ⊆ p '' H.support := by
    rintro y (rfl | rfl)
    · exact mem_image_of_mem _ hvw.mem_support_left
    · exact mem_image_of_mem _ hvw.mem_support_right
  have hright : ({p a, p b} : Set E) ⊆ p '' J.support := by
    rintro y (rfl | rfl)
    · exact mem_image_of_mem _ hab.mem_support_left
    · exact mem_image_of_mem _ hab.mem_support_right
  have hcommon : ({p v, p w} : Set E) ∩ {p a, p b} ⊆ {p q} := by
    have hsub := inter_subset_inter hleft hright
    rw [← image_inter hinj] at hsub
    simpa only [image_singleton] using hsub.trans (image_mono hsupport)
  have h := convexHull_mono hcommon (hinter (hHG hvw) (hJG hab) ⟨hx, hy⟩)
  simpa only [convexHull_singleton] using h

end SimpleGraph
