import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.finitePiecewiseAffineOn_capped_of_slab
    {S s b d T R : Set X} (hs : IsFinitePLBallPair E s b) (hd : IsFinitePLBallPair F d b)
    (A : X →ᵃ[ℝ] ℝ) {β : ℝ} (hsS : s ⊆ S)
    (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (Q J : SimplicialComplex ℝ X) (hQ : Q.faces.Finite) (hJ : J.faces.Finite)
    (hJR : J.space = R) (hneg : s ∩ {x | A x < 0} ⊆ Q.space)
    (f : X → X) (hfd : FinitePiecewiseAffineOn f d) (hfT : FinitePiecewiseAffineOn f T)
    (hQfix : ∀ x ∈ Q.space, f x = x) (hRfix : ∀ x ∈ R, f x = x)
    (hhigh : ∀ x, β ≤ A x → f x = x) :
    FinitePiecewiseAffineOn f (s ∪ d) := by
  classical
  have hscopy := hs
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hscopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLd, _⟩, _⟩, _⟩ := hdcopy
  obtain ⟨W, hW, hWspace⟩ := K.exists_finite_triangulation_inter_halfspaces hK
    {AffineMap.const ℝ X β - A}
  have hWs : W.space = s ∩ {x | β ≤ A x} := by
    rw [hWspace, hKs]
    congr 1
    ext x
    simp only [Finset.mem_singleton, forall_eq, mem_ofPred_eq]
    change (β - A x ≤ 0) ↔ β ≤ A x
    exact sub_nonpos
  have hfixedPL (Z : SimplicialComplex ℝ X) (hZ : Z.faces.Finite)
      (hfix : ∀ x ∈ Z.space, f x = x) : FinitePiecewiseAffineOn f Z.space := by
    apply ((Z.affineOnFaces_affine (ContinuousAffineMap.id ℝ X)).finitePiecewiseAffineOn hZ).congr
    exact fun x hx => (hfix x hx).symm
  have hfQ := hfixedPL Q hQ hQfix
  have hfR : FinitePiecewiseAffineOn f R := by
    rw [← hJR]
    exact hfixedPL J hJ (fun x hx => hRfix x (hJR.subset hx))
  have hfW := hfixedPL W hW (fun x hx => hhigh x (hWs.subset hx).2)
  have hfull := finitePiecewiseAffineOn_union
    (finitePiecewiseAffineOn_union (finitePiecewiseAffineOn_union hfd hfT) hfR)
    (finitePiecewiseAffineOn_union hfQ hfW)
  have hcover : s ∪ d ⊆ ((d ∪ T) ∪ R) ∪ (Q.space ∪ W.space) := by
    rintro x (hxs | hxd)
    · by_cases hn : A x < 0
      · exact Or.inr (Or.inl (hneg ⟨hxs, hn⟩))
      · by_cases hh : A x ≤ β
        · rcases hslab.symm.subset ⟨hsS hxs, le_of_not_gt hn, hh⟩ with hxT | hxR
          · exact Or.inl (Or.inl (Or.inr hxT))
          · exact Or.inl (Or.inr hxR)
        · exact Or.inr (Or.inr (hWs.symm.subset ⟨hxs, (lt_of_not_ge hh).le⟩))
    · exact Or.inl (Or.inl (Or.inl hxd))
  obtain ⟨V, hV, hVspace⟩ := K.exists_finite_triangulation_union L hK hL
  rw [hKs, hLd] at hVspace
  rw [← hVspace]
  exact hfull.restrict V hV (hVspace.subset.trans hcover)

end Set
