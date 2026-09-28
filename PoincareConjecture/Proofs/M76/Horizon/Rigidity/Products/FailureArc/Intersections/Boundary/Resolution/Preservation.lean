import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Pasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.RetainedCharts

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem pasted_boundary_disk_preserves_marks
    {E X : Type*} [TopologicalSpace X]
    {S N C Q H : Set E} {R O F : Set X} {f g k : E → X}
    (hcover : S ⊆ N ∪ C) (hNH : Disjoint N H)
    (hkN : EqOn k g N) (hkC : EqOn k f (S ∩ C))
    (hfR : MapsTo f S R) (hgR : MapsTo g N R) (hgO : MapsTo g N O)
    (hfproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ Q ∪ H)
    (hgproper : ∀ x ∈ N, g x ∈ frontier R ↔ x ∈ Q)
    (hfmark : MapsTo f (S ∩ Q) F) (hOmark : O ∩ frontier R ⊆ F) :
    MapsTo k S R ∧ EqOn k f (S ∩ H) ∧
      (∀ x ∈ S, k x ∈ frontier R ↔ x ∈ Q ∪ H) ∧ MapsTo k (S ∩ Q) F := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hcover hx with hn | hc
    · rw [hkN hn]
      exact hgR hn
    · rw [hkC ⟨hx, hc⟩]
      exact hfR hx
  · intro x hx
    exact hkC ⟨hx.1, (hcover hx.1).resolve_left (fun hn ↦ disjoint_left.mp hNH hn hx.2)⟩
  · intro x hx
    rcases hcover hx with hn | hc
    · rw [hkN hn, hgproper x hn]
      exact ⟨Or.inl, fun h ↦ h.resolve_right (fun hh ↦ disjoint_left.mp hNH hn hh)⟩
    · rw [hkC ⟨hx, hc⟩]
      exact hfproper x hx
  · intro x hx
    rcases hcover hx.1 with hn | hc
    · rw [hkN hn]
      exact hOmark ⟨hgO hn, (hgproper x hn).mpr hx.2⟩
    · rw [hkC ⟨hx.1, hc⟩]
      exact hfmark hx

theorem exists_open_agreement_of_boundary_disk_paste
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S N C qN W : Set P2} {A : Set X}
    {f g k : P2 → X}
    (hN : IsFinitePLBallPair P2 N qN) (hNS : N ⊆ S)
    (hcover : S ⊆ N ∪ C) (hcommon : N ∩ C = W)
    (hf : PolyhedralPLInCharts e f S) (hfi : InjOn f S)
    (hg : PolyhedralPLInCharts e g N) (hfix : EqOn g f W)
    (havoid : Disjoint (g '' N) A)
    (himage : k '' S = (g '' N) ∪ (f '' (S ∩ C))) :
    ∃ O : Set X, IsOpen O ∧ A ∩ (k '' S) ⊆ O ∧
      ∀ z ∈ O, z ∈ k '' S ↔ z ∈ f '' S := by
  have hwhole : S = N ∪ (S ∩ C) := by
    apply Subset.antisymm
    · intro x hx
      exact (hcover hx).elim Or.inl (fun hc ↦ Or.inr ⟨hx, hc⟩)
    · exact union_subset hNS inter_subset_left
  have hfold : f '' S = (f '' (S ∩ C)) ∪ (f '' N) := by
    conv_lhs => rw [hwhole, image_union]
    exact union_comm _ _
  have hknew : k '' S = (f '' (S ∩ C)) ∪ (g '' N) := himage.trans (union_comm _ _)
  have hseam : (f '' (S ∩ C)) ∩ (f '' N) ⊆ g '' N := by
    rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    have hxy := hfi hx.1 (hNS hy) (hxz.trans hyz.symm)
    subst y
    exact ⟨x, hy, (hfix (hcommon.subset ⟨hy, hx.2⟩)).trans hxz⟩
  exact exists_open_agreement_of_compact_replacement
    (hN.isCompact.image_of_continuousOn (hf.continuousOn.mono hNS)).isClosed
    (hN.isCompact.image_of_continuousOn hg.continuousOn).isClosed hfold hknew hseam havoid

end PoincareConjecture.M76.Dehn.Annuli
