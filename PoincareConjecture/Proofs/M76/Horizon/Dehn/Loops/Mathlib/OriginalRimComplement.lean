import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.StripEndCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripExteriorRims











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)




theorem original_rim_complement_is_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q A M C : Set E} (hS : IsFinitePLBallPair P2 S Q)
    (c : Bool → P2 → E)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hAM : Disjoint A M) (hAC : Disjoint A C)
    (hcover : ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1)
    (h0A : (c false '' source) ∩ A = c false '' arm u)
    (hA1 : Disjoint A (c true '' source))
    (hAI : IsFinitePLBallPair ℝ (A ∩ Q) {c false (0, u), c false (1, u)})
    (hab : c false (0, u) ≠ c false (1, u)) :
    let V := ((M ∩ Q) ∪ (C ∩ Q)) ∪ ((c false '' stripEnds) ∪ (c true '' stripEnds))
    IsFinitePLBallPair ℝ V {c false (0, u), c false (1, u)} ∧
      (A ∩ Q) ∪ V = Q ∧
      (A ∩ Q) ∩ V = {c false (0, u), c false (1, u)} := by
  let U := A ∩ Q
  let V := ((M ∩ Q) ∪ (C ∩ Q)) ∪ ((c false '' stripEnds) ∪ (c true '' stripEnds))
  have hend (i : Bool) : (c i '' source) ∩ Q = c i '' stripEnds :=
    embedded_strip_inter_old_rim (c i) (hcQ i)
  have hUVcover : U ∪ V = Q := by
    ext x
    constructor
    · rintro (hx | (hx | hx) | hx | hx)
      · exact hx.2
      · exact hx.2
      · exact hx.2
      · exact ((hend false).symm.subset hx).2
      · exact ((hend true).symm.subset hx).2
    · intro hx
      have hxS := hS.1 hx
      rw [← hcover] at hxS
      rcases hxS with ((hxA | hxM) | hxC) | hx0 | hx1
      · exact Or.inl ⟨hxA, hx⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hxM, hx⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hxC, hx⟩))
      · exact Or.inr (Or.inr (Or.inl ((hend false).subset ⟨hx0, hx⟩)))
      · exact Or.inr (Or.inr (Or.inr ((hend true).subset ⟨hx1, hx⟩)))
  have hUVinter : U ∩ V = {c false (0, u), c false (1, u)} := by
    have harmQ := embedded_strip_arm_inter_old_rim (c false) (hcQ false) u hu
    ext x
    constructor
    · rintro ⟨hxU, (hx | hx) | hx | hx⟩
      · exact (Set.disjoint_left.mp hAM hxU.1 hx.1).elim
      · exact (Set.disjoint_left.mp hAC hxU.1 hx.1).elim
      · exact harmQ.subset ⟨h0A.subset ⟨((hend false).symm.subset hx).1, hxU.1⟩,
          hxU.2⟩
      · exact (Set.disjoint_left.mp hA1 hxU.1 ((hend true).symm.subset hx).1).elim
    · intro hx
      have hxU := hAI.1 hx
      have hxArm := (harmQ.symm.subset hx).1
      exact ⟨hxU, Or.inr (Or.inl ((hend false).subset
        ⟨(h0A.symm.subset hxArm).1, hxU.2⟩))⟩
  obtain ⟨W, hW, hUW, hUWinter⟩ :=
    hS.exists_boundary_arc_complement hAI inter_subset_right hab
  have hWV : W = V := by
    apply Subset.antisymm
    · intro x hxW
      have hxQ := hUW.subset (Or.inr hxW)
      rcases hUVcover.symm.subset hxQ with hxU | hxV
      · exact (hUVinter.symm.subset (hUWinter.subset ⟨hxU, hxW⟩)).2
      · exact hxV
    · intro x hxV
      have hxQ := hUVcover.subset (Or.inr hxV)
      rcases hUW.symm.subset hxQ with hxU | hxW
      · exact (hUWinter.symm.subset (hUVinter.subset ⟨hxU, hxV⟩)).2
      · exact hxW
  refine ⟨?_, hUVcover, hUVinter⟩
  simpa only [hWV] using hW

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
