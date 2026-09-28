import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCut
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityTransport
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle









set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem exists_disjoint_polygon_family_of_closed_cut
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {s₀ s₁ : Set E} (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hsep : Disjoint s₀ s₁) (hcover : s₀ ∪ s₁ = ⋃ i, (P i).boundary ℝ) :
    ∃ I : Set ι,
      s₀ = ⋃ i : I, (P i).boundary ℝ ∧
      s₁ = ⋃ i : (Iᶜ : Set ι), (P i).boundary ℝ ∧
      Pairwise (fun i j : I => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) ∧
      Pairwise (fun i j : (Iᶜ : Set ι) =>
        Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) := by
  have hpre (i : ι) : IsPreconnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hPe i) (hPi i)
    exact (isConnected_iff_connectedSpace.mpr
      (e.connectedSpace_iff.mpr inferInstance)).isPreconnected
  obtain ⟨I, _, _, h₀, h₁⟩ := exists_connected_cut_partition hs₀ hs₁
    (fun i => (P i).boundary ℝ) hpre
    (fun i x hx => hcover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩))
    (fun _ => by rw [hsep.inter_eq, inter_empty])
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · rw [← hcover, union_inter_cancel_left] at h₀
    exact h₀
  · rw [← hcover, union_inter_cancel_right] at h₁
    exact h₁
  · intro i j hij
    exact hpair (fun h => hij (Subtype.ext h))
  · intro i j hij
    exact hpair (fun h => hij (Subtype.ext h))




theorem exists_disjoint_finitePL_image_family
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {s : Set E} {t : Set F} (hcover : s = ⋃ i, (P i).boundary ℝ)
    (e : s ≃ₜ t) (he : e.IsFinitePL) :
    ∃ (N : ι → ℕ) (Q : ∀ i, Polygon F (N i + 3)),
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      t = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ)) := by
  have hsrc : s = (∅ : Set E) ∪ ⋃ i, (P i).boundary ℝ := by
    simpa only [empty_union] using hcover
  have hp : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ (∅ : Set E)) := by
    intro i j hij
    rw [(hpair hij).inter_eq]
  obtain ⟨f, N, Q, _, _, hQ, htarget, htargetPair⟩ :=
    exists_finitePL_image_family n P hPe hPi hsrc hp e he
  refine ⟨N, Q, fun i => ⟨(hQ i).1, (hQ i).2.1⟩, ?_, ?_⟩
  · simpa only [image_empty, empty_union] using htarget
  · intro i j hij
    apply disjoint_iff_inter_eq_empty.mpr
    exact subset_empty_iff.mp (by simpa only [image_empty] using htargetPair hij)





theorem exists_disjoint_finitePL_remainder_family
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {b X : Set E} {Y : Set F} (hb : IsClosed b)
    (hsep : Disjoint b X) (hcover : b ∪ X = ⋃ i, (P i).boundary ℝ)
    (e : X ≃ₜ Y) (he : e.IsFinitePL) :
    ∃ (I : Set ι) (N : I → ℕ) (Q : ∀ i, Polygon F (N i + 3)),
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges) ∧
      Y = ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => Disjoint ((Q i).boundary ℝ) ((Q j).boundary ℝ)) := by
  have hcopy := he
  obtain ⟨_, ⟨K, hK, hKX, _⟩, _⟩ := hcopy
  have hX : IsClosed X := by
    rw [← hKX]
    exact (K.isCompact_space_of_finite hK).isClosed
  obtain ⟨I, _, hIX, _, hIpair⟩ := exists_disjoint_polygon_family_of_closed_cut
    n P hPe hPi hpair hb hX hsep hcover
  obtain ⟨N, Q, hQ, hY, hQpair⟩ := exists_disjoint_finitePL_image_family
    (fun i : (Iᶜ : Set ι) => n i) (fun i => P i)
    (fun i => hPe i) (fun i => hPi i) hIpair hIX e he
  exact ⟨Iᶜ, N, Q, hQ, hY, hQpair⟩

end Polygon
