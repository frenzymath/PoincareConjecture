import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SeparatedSource

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SeparatedCircleSource.exists_selected_components
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁) (hc₀ : IsConnected C₀)
    (himage : f₀ '' C₀ = f₁ '' C₁) :
    ∃ i : D.decomposition.Index, D.decomposition.pieces i = C₀ ∧
      D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁ ∧
      D.decomposition.mate i ≠ i := by
  classical
  let old := D.decomposition
  have hsub₀ : C₀ ⊆ D.first.space := D.first_selected.trans interior_subset
  have hsub₁ : D.shift '' C₁ ⊆ D.shift '' D.second.space :=
    image_mono (D.second_selected.trans interior_subset)
  have hdis : Disjoint C₀ (D.shift '' C₁) := D.disjoint.mono hsub₀ hsub₁
  have hcover : old.graph.space = C₀ ∪ D.shift '' C₁ := old.space.trans D.double_space
  obtain ⟨i,hi⟩ := hc₀.exists_closure_subset_of_finite_closed_cover old.pieces
    (fun i => (old.pieces_isCompact i).isClosed)
    (by
      intro x hx
      exact old.cover.subset (hcover.symm.subset (Or.inl hx)))
    (g := ∅) (fun i j hij => (disjoint_iff_inter_eq_empty.mp (old.disjoint hij)).subset)
    (disjoint_empty _)
  have hCi : C₀ ⊆ old.pieces i := subset_closure.trans hi
  have hiC : old.pieces i ⊆ C₀ := by
    have hp : old.pieces i ⊆ C₀ ∪ D.shift '' C₁ :=
      (old.piece_subset_double i).trans D.double_space.subset
    have hcase := isPreconnected_iff_subset_of_disjoint_closed.mp
      (old.pieces_isConnected i).isPreconnected C₀ (D.shift '' C₁)
      hC₀.isClosed (hC₁.image D.shift.continuous).isClosed hp
      (by rw [hdis.inter_eq,inter_empty])
    rcases hcase with h | h
    · exact h
    · obtain ⟨x,hx⟩ := hc₀.nonempty
      exact (disjoint_left.mp hdis hx (h (hCi hx))).elim
  have hiEq : old.pieces i = C₀ := Subset.antisymm hiC hCi
  have hmate : old.mate i ≠ i := by
    intro hm
    obtain ⟨x,hx⟩ := hc₀.nonempty
    have hxG := old.space.symm.subset (old.piece_subset_double i (hCi hx))
    have hp := (old.partner_component i ⟨x,hxG⟩).mp (hCi hx)
    change (old.partner ⟨x,hxG⟩ : P2) ∈ old.pieces (old.mate i) at hp
    rw [hm,hiEq] at hp
    exact old.free ⟨x,hxG⟩ (D.first_injective (hsub₀ hp) (hsub₀ hx) (old.value ⟨x,hxG⟩))
  have hmateC : old.pieces (old.mate i) = D.shift '' C₁ := by
    apply Subset.antisymm
    · intro x hx
      rcases D.double_space.subset (old.piece_subset_double (old.mate i) hx) with h | h
      · exact (disjoint_left.mp (old.disjoint hmate) hx (hCi h)).elim
      · exact h
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨x,hx,hxy⟩ := himage.symm.subset ⟨y,hy,rfl⟩
      have hyS : D.shift y ∈ D.source.space := D.source_space.symm.subset
        (Or.inr ⟨y,interior_subset (D.second_selected hy),rfl⟩)
      have hvalue : D.map x = D.map (D.shift y) :=
        (D.first_value (hsub₀ hx)).trans (hxy.trans
          (D.second_value y (interior_subset (D.second_selected hy))).symm)
      have hm := (old.piece_image_preimage i (D.shift y) hyS).mp ⟨x,hCi hx,hvalue⟩
      exact hm.resolve_left (fun h => disjoint_left.mp hdis (hiC h) ⟨y,hy,rfl⟩)
  exact ⟨i,hiEq,hmateC,hmate⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
