import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.RectangleConnectedSides
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.FinitePLProductBandGluing

/-!
# Gluing actual rectangle patches by their common height intervals

Every nonempty intersection of distinct patches has a full height
interval chart on their vertical boundaries. This forces constant
side membership after bottom normalization and injective height on
the overlap, supplying the finite product-band gluing theorem.
See Alexander 1924, pp. 6--8 and M76 derivation 271.
-/

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

/-- Finite height rectangles glue over their entire actual
union when each nonempty distinct overlap is a full height
interval on the vertical boundary. No transition agreement
or fixed overlap membership is assumed. See Alexander
pp. 6--8 and M76 derivation 271. -/
theorem exists_iUnion_rectangle_height_product
    (T : ι → Set E) (A : E → ℝ) {α β : ℝ} (hαβ : α < β)
    (G : ∀ i, (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T i)
    (hG : ∀ i, (G i).IsFinitePL)
    (hheight : ∀ i p, A (G i p) = (p : ℝ × ℝ).2)
    (hover : ∀ i j, i ≠ j → (T i ∩ T j).Nonempty →
      ∃ d : Icc α β ≃ₜ (T i ∩ T j : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i j, i ≠ j → ∀ p, (G i p : E) ∈ T j →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1) :
    ∃ H : (((⋃ i, T i) ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ
        (⋃ i, T i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      ∀ (x : E) (hx : x ∈ (⋃ i, T i) ∩ {x | A x = α}),
        (H ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x := by
  classical
  have hex (i : ι) := (hG i).exists_bottom_normalized_rectangle_chart_with_overlaps
    hαβ A (hheight i) (fun j : {j : ι // i ≠ j} => T j.val)
      (fun j => hover i j.val j.property)
      (fun j => hboundary i j.val j.property)
  choose C hC hCA hbase hmem using hex
  have hoverlap (i j : ι) (p : ((T i ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ))) :
      (C i p : E) ∈ T j ↔ (p : E × ℝ).1 ∈ T j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true (C i p).property p.property.1.1
    · exact hmem i ⟨j, hij⟩ p
  have hinj (i j : ι) (hij : i ≠ j) : InjOn A (T i ∩ T j) := by
    intro x hx y hy hxy
    obtain ⟨d, hd⟩ := hover i j hij ⟨x, hx⟩
    let t := d.symm ⟨x, hx⟩
    let s := d.symm ⟨y, hy⟩
    have ht : (d t : E) = x := congrArg Subtype.val (d.apply_symm_apply _)
    have hs : (d s : E) = y := congrArg Subtype.val (d.apply_symm_apply _)
    have hts : t = s := Subtype.ext
      ((hd t).symm.trans ((congrArg A ht).trans
        (hxy.trans ((congrArg A hs).symm.trans (hd s)))))
    exact ht.symm.trans ((congrArg (fun u => (d u : E)) hts).trans hs)
  obtain ⟨H, hH, hHA, hbottom, _⟩ :=
    exists_iUnion_height_product T A hαβ.le C hC hCA hbase hoverlap hinj
  exact ⟨H, hH, hHA, hbottom⟩

end Homeomorph
