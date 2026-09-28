import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoMarkedBall

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem exists_hamilton_indexTwo_marked_target
    {ι : Type*} [Fintype ι] (F : HamiltonIndexTwoFrame ι)
    (S : HamiltonIndexTwoMarkedBall F)
    (P : Set (ι → ℝ)) (delta : Bool → Set (ι → ℝ))
    (hPL : P ⊆ Icc F.lower F.upper)
    (hPfront : P ∩ frontier (Icc F.lower F.upper) = F.side)
    (hdP : ∀ j, delta j ⊆ P)
    (hdside : ∀ j, delta j ∩ F.side = F.rim j)
    (hdisjoint : Disjoint (delta false) (delta true))
    (A : (ι → ℝ) ≃ₜ (ι → ℝ))
    (hAfix : EqOn A id (interior (Icc F.lower F.upper))ᶜ)
    (hball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (A '' P)
      ((F.side ∪ A '' delta false) ∪ A '' delta true))
    (hdisk : ∀ j, IsFinitePLBallPair (ℝ × ℝ) (A '' delta j) (F.rim j)) :
    ∃ T : HamiltonIndexTwoMarkedBall F,
      T.carrier = A '' P ∧ ∀ j, T.disk j = A '' delta j := by
  have hfrontfix (x : ι → ℝ) (hx : x ∈ frontier (Icc F.lower F.upper)) : A x = x :=
    hAfix hx.2
  have hside : F.side ⊆ frontier (Icc F.lower F.upper) :=
    fun _ hx => F.frontier_eq.symm.subset (Or.inl (Or.inl hx))
  have houter (j : Bool) : F.outer j ⊆ frontier (Icc F.lower F.upper) := by
    intro x hx
    apply F.frontier_eq.symm.subset
    cases j with
    | false => exact Or.inl (Or.inr hx)
    | true => exact Or.inr hx
  have hrim (j : Bool) : F.rim j ⊆ F.side :=
    fun _ hx => ((S.disk_side j).symm.subset hx).2
  have himage (s : Set (ι → ℝ)) (hs : s ⊆ frontier (Icc F.lower F.upper)) :
      A '' s = s := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rwa [hfrontfix x (hs hx)]
    · intro x hx
      exact ⟨x, hx, hfrontfix x (hs hx)⟩
  have hAL : A '' P ⊆ Icc F.lower F.upper := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have hfix : A (A x) = A x :=
      hAfix (fun hi => hnot (interior_subset hi))
    have heq : A x = x := A.injective hfix
    exact hnot (heq.symm ▸ hPL hx)
  have hdouter (j : Bool) : delta j ∩ F.outer j = F.rim j := by
    apply Subset.antisymm
    · intro x hx
      have hxside : x ∈ F.side := hPfront.subset ⟨hdP j hx.1, houter j hx.2⟩
      exact (hdside j).subset ⟨hx.1, hxside⟩
    · intro x hx
      exact ⟨((hdside j).symm.subset hx).1, (F.outerBall j).1 hx⟩
  refine ⟨{
    carrier := A '' P
    disk := fun j => A '' delta j
    ball := hball
    subset_box := hAL
    diskBall := hdisk
    disk_outer := ?_
    disk_side := ?_
    disksDisjoint := ?_
    boundary_outer := ?_
  }, rfl, fun _ => rfl⟩
  · intro j
    rw [← himage (F.outer j) (houter j), ← image_inter A.injective,
      hdouter j, himage (F.rim j) ((hrim j).trans hside)]
  · intro j
    rw [← himage F.side hside, ← image_inter A.injective,
      hdside j, himage (F.rim j) ((hrim j).trans hside)]
  · apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x := A.injective heq
    exact Set.disjoint_left.mp hdisjoint hx (hyx ▸ hy)
  · intro j
    apply Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, heq⟩ := hball.1 hx.1
      have hyx : y = x := A.injective (heq.trans (hfrontfix x (houter j hx.2)).symm)
      have hxP : x ∈ P := hyx ▸ hy
      have hxside : x ∈ F.side := hPfront.subset ⟨hxP, houter j hx.2⟩
      exact (S.boundary_outer j).subset ⟨Or.inl (Or.inl hxside), hx.2⟩
    · intro x hx
      refine ⟨?_, (F.outerBall j).1 hx⟩
      have hxd : x ∈ A '' delta j := (hdisk j).1 hx
      cases j with
      | false => exact Or.inl (Or.inr hxd)
      | true => exact Or.inr hxd

end PoincareConjecture.M76
