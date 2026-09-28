import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutGraphSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphSectionHomotopy








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.CutGraph

local notation "V3" => (Fin 3 → ℝ)

theorem exists_homotopy_section_of_closed_cut_collapse
    {X V I ι : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {e : ι → OpenPartialHomeomorph X V3}
    (R : Set X) (D : V → Set X) (C : I → Set X)
    (hD : ∀ v, PLDomain e (D v)) (hconn : ∀ v, IsConnected (D v))
    (hDR : ∀ v, D v ⊆ R) (hCR : ∀ i, C i ⊆ R)
    (Y : I → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, Nonempty (Y i)]
    (W : ∀ i, (Y i × unitInterval) ≃ₜ C i) (ends : I → Bool → V)
    (hport : ∀ i b y, (W i (y, if b then 1 else 0) : X) ∈ D (ends i b))
    (q : C(R, carrier ends))
    (hqD : ∀ v (x : R), (x : X) ∈ D v → (q x : Ambient V I) = vertex v)
    (hqC : ∀ i (x : R) (hi : (x : X) ∈ C i),
      q x = edgePath ends i (((W i).symm ⟨x, hi⟩).2)) :
    ∃ s : C(carrier ends, R), (q.comp s).Homotopic (ContinuousMap.id (carrier ends)) := by
  obtain ⟨p, y, s, hsv, hsa, hsk⟩ := exists_closed_cut_graph_section R D C hD hconn
    hDR hCR Y W ends hport
  refine ⟨s, homotopic_id_of_collapsed_segments ends (q.comp s) ?_ ?_ ?_⟩
  · intro v x hx
    apply hqD v (s x)
    rw [hsv v x hx]
    exact (p v).property
  · intro i b x hx
    exact hqD (ends i b) (s x) (hsa i b x hx)
  · intro i x hx
    let t := faceCoordinate (J := Coordinate V I)
      {Sum.inr (i, false), Sum.inr (i, true)} (Sum.inr (i, true))
      ⟨(x : Ambient V I), hx⟩
    have he : (s x : X) = W i (y i, t) := hsk i x hx
    have hi : (s x : X) ∈ C i := he ▸ (W i (y i, t)).property
    change q (s x) = edgePath ends i t
    rw [hqC i (s x) hi]
    have he' : (⟨s x, hi⟩ : C i) = W i (y i, t) := Subtype.ext he
    rw [he', (W i).symm_apply_apply]

end PoincareConjecture.M76.CutGraph
