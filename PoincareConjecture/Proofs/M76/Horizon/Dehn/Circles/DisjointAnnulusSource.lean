import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedAnnulusSource
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.DisjointSourceDisk

set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1

def exchangedCircleHomeomorph {A : Bool → Type*} [∀ i, TopologicalSpace (A i)]
    (e : A false ≃ₜ A true) : (i : Bool) → A (!i) ≃ₜ A i
  | false => e.symm
  | true => e

theorem disjoint_annulus_source_partition {m n : Bool → ℕ}
    (P : (i : Bool) → Polygon V2 (m i + 3)) (I : (i : Bool) → Polygon V2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinjP : ∀ i, Function.Injective (P i))
    (hI : ∀ i, (I i).HasSimplicialEdges) (hinjI : ∀ i, Function.Injective (I i))
    (hPsq : ∀ i, (P i).boundary ℝ ⊆ ball 0 1)
    (hIP : ∀ i, closure (I i).inside ⊆ (P i).inside)
    (hdis : Disjoint (closure (P false).inside) (closure (P true).inside)) :
    let S := fun i => closure (I i).inside
    let C := fun i => closure (P i).inside \ (I i).inside
    let O := D \ ((P false).inside ∪ (P true).inside)
    ((S false ∪ S true) ∪ O) ∪ (C false ∪ C true) = D ∧
      (∀ i, S i ∩ C i = (I i).boundary ℝ) ∧
      (∀ i, C i ∩ O = (P i).boundary ℝ) ∧
      Disjoint (S false) (S true) ∧ Disjoint (S false ∪ S true) O ∧
      Disjoint (C false) (C true) ∧
      (∀ i, Disjoint (S (!i)) (C i)) ∧
      (∀ i, IsClosed (C i)) ∧ IsClosed O ∧
      (∀ i, S i ⊆ ball 0 1) ∧ (∀ i, C i ⊆ ball 0 1) ∧ R ⊆ O := by
  dsimp
  have hregion (i : Bool) := polygon_source_region (P i)
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (hP i) (hinjP i) (convex_ball _ _) (hPsq i)
  have hpart (i : Bool) := nested_annulus_source_partition (P i) (I i)
    (hP i) (hinjP i) (hI i) (hinjI i) (hPsq i) (hIP i)
  have hSP (i : Bool) : closure (I i).inside ⊆ closure (P i).inside := (hIP i).trans subset_closure
  have hO (i : Bool) : D \ ((P false).inside ∪ (P true).inside) ⊆ D \ (P i).inside := by
    intro x hx
    cases i
    · exact ⟨hx.1, fun hi => hx.2 (Or.inl hi)⟩
    · exact ⟨hx.1, fun hi => hx.2 (Or.inr hi)⟩
  have hPpair (i : Bool) : Disjoint (closure (P (!i)).inside) (closure (P i).inside) := by
    cases i
    · exact hdis.symm
    · exact hdis
  have hbdC (i : Bool) : (P i).boundary ℝ ⊆ closure (P i).inside \ (I i).inside :=
    fun _ hx => ((hpart i).2.2.1.symm ▸ hx).1
  refine ⟨?_, fun i => (hpart i).2.1, ?_, hdis.mono (hSP false) (hSP true), ?_,
    hdis.mono sdiff_subset sdiff_subset, ?_, fun i => (hpart i).2.2.2.2.1, ?_,
    fun i => (hSP i).trans (hregion i).2.2.2, fun i => sdiff_subset.trans (hregion i).2.2.2, ?_⟩
  · apply Subset.antisymm
    · exact union_subset
        (union_subset (union_subset
          ((hSP false).trans ((hregion false).2.2.2.trans ball_subset_closedBall))
          ((hSP true).trans ((hregion true).2.2.2.trans ball_subset_closedBall))) sdiff_subset)
        (union_subset (sdiff_subset.trans ((hregion false).2.2.2.trans ball_subset_closedBall))
          (sdiff_subset.trans ((hregion true).2.2.2.trans ball_subset_closedBall)))
    · intro x hx
      by_cases hp0 : x ∈ (P false).inside
      · by_cases hi0 : x ∈ (I false).inside
        · exact Or.inl (Or.inl (Or.inl (subset_closure hi0)))
        · exact Or.inr (Or.inl ⟨subset_closure hp0, hi0⟩)
      by_cases hp1 : x ∈ (P true).inside
      · by_cases hi1 : x ∈ (I true).inside
        · exact Or.inl (Or.inl (Or.inr (subset_closure hi1)))
        · exact Or.inr (Or.inr ⟨subset_closure hp1, hi1⟩)
      exact Or.inl (Or.inr ⟨hx, fun h => h.elim hp0 hp1⟩)
  · intro i
    ext x
    constructor
    · exact fun hx => (hpart i).2.2.1 ▸ ⟨hx.1, hO i hx.2⟩
    · intro hx
      have hxC := hbdC i hx
      have hxnot : x ∉ (P i).inside := ((hpart i).2.2.1.symm ▸ hx).2.2
      have hxother : x ∉ (P (!i)).inside := fun ho =>
        Set.disjoint_left.mp (hPpair i) (subset_closure ho) hxC.1
      refine ⟨hxC, (hregion i).2.2.2.trans ball_subset_closedBall hxC.1, ?_⟩
      cases i <;> exact fun h => h.elim (by assumption) (by assumption)
  · apply Set.disjoint_left.mpr
    rintro x (hx | hx) ho
    · exact (hO false ho).2 (hIP false hx)
    · exact (hO true ho).2 (hIP true hx)
  · intro i
    exact (hPpair i).mono (hSP (!i)) sdiff_subset
  · exact isClosed_closedBall.sdiff
      (((hregion false).2.1 ▸ isOpen_interior).union ((hregion true).2.1 ▸ isOpen_interior))
  · intro x hx
    exact ⟨sphere_subset_closedBall hx, fun h => h.elim
      ((hpart false).2.2.2.2.2.2 hx).2 ((hpart true).2.2.2.2.2.2 hx).2⟩

end Dehn
