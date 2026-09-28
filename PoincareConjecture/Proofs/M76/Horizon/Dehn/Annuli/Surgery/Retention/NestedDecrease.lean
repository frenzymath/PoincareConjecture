import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CollarComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.NestedRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ComponentCount

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder

local notation "P2" => (ℝ × ℝ)
local notation "Cyl" => Set.prod (sphere (0 : Fin 2 → ℝ) 1) (Icc (-1 : ℝ) 1)

theorem double_component_count_lt
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {l r L d : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l r (A k)} {j : Fin 2}
    {f : P2 → X} {τ : (P2 × ℝ) → X}
    (D : NestedResolvingCylinder (L := L) (d := d) e B j f τ)
    (M : SourceCircleDecomposition f (squareAnnulus L d)) (i : Fin 2 → M.Index)
    (hr : 0 < r) (hnested : closure (B j.rev).outer.inside ⊆ (B j).inner.inside)
    (hmiddle : ∀ k, (fun p : squareAnnulus l r ↦ ((B k).chart p : P2)) ''
      {p | depth l p = 0} = M.pieces (i k))
    (htrace : ∀ k x, x ∈ A k → x ∈ doubleLocusOn f (squareAnnulus L d) →
      x ∈ M.pieces (i k)) :
    Nat.card (ConnectedComponents (doubleLocusOn D.map Cyl)) <
      Nat.card (ConnectedComponents (doubleLocusOn f (squareAnnulus L d))) := by
  have hdepth : ∀ k (p : squareAnnulus l r),
      ((B k).chart p : P2) ∈ doubleLocusOn f (squareAnnulus L d) → depth l p = 0 := by
    intro k p hx
    obtain ⟨q, hq, heq⟩ := (hmiddle k).symm.subset
      (htrace k ((B k).chart p) ((B k).chart p).property hx)
    have hqp : q = p := (B k).chart.injective (Subtype.ext heq)
    exact hqp ▸ hq
  obtain ⟨hwhole, _, hremoved, _⟩ := M.nested_essential_component_retention (i j) (i j.rev)
    (B j) (B j.rev) hr hr hnested (hmiddle j) (hmiddle j.rev) (htrace j) (htrace j.rev)
  obtain ⟨c, U, V, H, hci, hcc, _, _, _, _, _, _, _, hnew, _⟩ :=
    D.exists_retained_source hr hnested hdepth
  exact M.retained_component_count_lt (union_subset D.outer_source D.inner_source)
    hwhole c hci hcc hnew (i j) hremoved

end PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder
