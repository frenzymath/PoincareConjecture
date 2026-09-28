import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Contacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.DoubleTrace
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.LiteralPartner

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

variable {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)

def retainedSource : Set P2 :=
  ((E.first \ interior D) ∪ (E.middle \ interior D)) ∪ (E.last \ interior D)

theorem retainedSource_subset : E.retainedSource ⊆ T \ interior D := by
  rintro x ((hx | hx) | hx)
  · exact ⟨E.retained_subset .first hx.1, hx.2⟩
  · exact ⟨E.retained_subset .middle hx.1, hx.2⟩
  · exact ⟨E.retained_subset .last hx.1, hx.2⟩

theorem center_disjoint_retainedSource (hci : ∀ j, InjOn (c j) source) (j : Bool) :
    Disjoint (c j '' arm 0) E.retainedSource := by
  apply disjoint_left.mpr
  intro x hx hxE
  have hxS : x ∈ c j '' source := image_mono
    ((arm_zero_subset_halfSource false).trans (halfSource_subset_source false)) hx
  cases j
  · rcases hxE with (hxE | hxE) | hxE
    · exact disjoint_left.mp (disjoint_center_far_images (c false) (hci false) (!E.s0)) hx
        (E.strip_first.subset ⟨hxS, hxE.1⟩)
    · exact disjoint_left.mp (disjoint_center_far_images (c false) (hci false) E.s0) hx
        (E.strip_middle0.subset ⟨hxS, hxE.1⟩)
    · exact disjoint_left.mp E.opposite_last hxE.1 hxS
  · rcases hxE with (hxE | hxE) | hxE
    · exact disjoint_left.mp E.opposite_first hxE.1 hxS
    · exact disjoint_left.mp (disjoint_center_far_images (c true) (hci true) E.s1) hx
        (E.strip_middle1.subset ⟨hxS, hxE.1⟩)
    · exact disjoint_left.mp (disjoint_center_far_images (c true) (hci true) (!E.s1)) hx
        (E.strip_last.subset ⟨hxS, hxE.1⟩)

theorem whole_component_retention
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {f : P2 → X} {τ : C3 → X} {Q : Set P2} {R : Set X}
    (K : SourceDoubleComponents e f (T \ interior D) Q R)
    (hci : ∀ j, InjOn (c j) source)
    (hcS : ∀ j, MapsTo (c j) source (T \ interior D))
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior D) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (selected : Bool → K.Index) (hcenter : ∀ j, c j '' arm 0 = K.pieces (selected j)) :
    (∀ k, K.pieces k ⊆ E.retainedSource ∨ Disjoint (K.pieces k) E.retainedSource) ∧
      (∀ j, Disjoint (K.pieces (selected j)) E.retainedSource ∧
        ¬ K.pieces (selected j) ⊆ E.retainedSource) ∧
      (∀ k, (∀ j, k ≠ selected j) → K.pieces k ⊆ E.retainedSource) := by
  classical
  have hremoved (j : Bool) : Disjoint (K.pieces (selected j)) E.retainedSource :=
    hcenter j ▸ E.center_disjoint_retainedSource hci j
  have hkept (k : K.Index) (hk : ∀ j, k ≠ selected j) : K.pieces k ⊆ E.retainedSource := by
    have hstrip (j : Bool) : Disjoint (K.pieces k) (c j '' source) := by
      apply disjoint_left.mpr
      intro x hx hxS
      have hxdouble : x ∈ doubleLocusOn f (T \ interior D) := K.space ▸ K.pieces_subset k hx
      have hxC := (original_strip_double_trace c hcS hdis hτ h0 h1 hfull j).subset ⟨hxS, hxdouble⟩
      exact disjoint_left.mp (K.disjoint (hk j)) hx (hcenter j ▸ hxC)
    intro x hx
    have hxold : x ∈ T \ interior D := (K.space ▸ K.pieces_subset k hx).1
    have hout : x ∈ (E.first ∪ E.middle) ∪ E.last :=
      (E.cover.symm.subset hxold.1).resolve_right (by
        rintro (hh | hh)
        · exact disjoint_left.mp (hstrip false) hx hh
        · exact disjoint_left.mp (hstrip true) hx hh)
    rcases hout with (hh | hh) | hh
    · exact Or.inl (Or.inl ⟨hh, hxold.2⟩)
    · exact Or.inl (Or.inr ⟨hh, hxold.2⟩)
    · exact Or.inr ⟨hh, hxold.2⟩
  refine ⟨?_, ?_, hkept⟩
  · intro k
    by_cases hk : ∃ j, k = selected j
    · obtain ⟨j, rfl⟩ := hk
      exact Or.inr (hremoved j)
    · exact Or.inl (hkept k (fun j hh ↦ hk ⟨j, hh⟩))
  · intro j
    refine ⟨hremoved j, ?_⟩
    intro hsub
    obtain ⟨x, hx⟩ := (K.connected (selected j)).nonempty
    exact disjoint_left.mp (hremoved j) hx (hsub hx)

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
