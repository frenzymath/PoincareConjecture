import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents









set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [AddCommGroup E] [Module ℝ E]



theorem segmentCarrier_mono {G H : SimpleGraph V} (hGH : G ≤ H) (p : V → E) :
    G.segmentCarrier p ⊆ H.segmentCarrier p := by
  rintro x ⟨v, w, hvw, hx⟩
  exact ⟨v, w, hGH hvw, hx⟩





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
