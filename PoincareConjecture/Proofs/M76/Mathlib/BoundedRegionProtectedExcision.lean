import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBoundaryCollar
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionCylinderProtection

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.excision_of_spherical_balls_in_top_face
    {B O s I b c d q : Set (X × ℝ)} {D : Set X}
    (hdim : Module.finrank ℝ X = 3)
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (c ∪ d))
    (hO : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) O (c ∪ d))
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hI : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) I (b ∪ d))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hsB : s ⊆ B) (hOI : O ⊆ I)
    (hsI : s ∩ I = b ∪ d) (hBO : B ∩ O = c ∪ d) (hsO : s ∩ O = d)
    (hcover : B ∪ O = frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (hinner : s ∪ I = frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (hstop : s ⊆ interior D ×ˢ {(1 : ℝ)})
    (K : SimplicialComplex ℝ X) (hK : K.faces.Finite)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hKD : K.space = D) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (B \ s)) (b ∪ c) := by
  let S := frontier (D ×ˢ Icc (-1 : ℝ) 1)
  let T := interior D ×ˢ {(1 : ℝ)}
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_triangulation_cylinder_nonTop
    hK hD hcv hne hKD
  have hJI : J.space ⊆ I := by
    intro x hxJ
    have hx := hJs.subset hxJ
    exact (hinner.symm.subset hx.1).resolve_left (fun hxs => hx.2 (hstop hxs))
  have hOcopy := hO
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLO, _⟩, _⟩, _⟩ := hOcopy
  obtain ⟨Q, hQ, hQs⟩ := L.exists_finite_triangulation_union J hL hJ
  have hQI : Q.space ⊆ I := by
    rw [hQs, hLO]
    exact union_subset hOI hJI
  have hQb : Q.space ∩ b ⊆ q := by
    rintro x ⟨hxQ, hxb⟩
    rcases hQs.subset hxQ with hxL | hxJ
    · have hxd : x ∈ d := hsO.subset ⟨hs.1 (Or.inl hxb), hLO.subset hxL⟩
      exact hbd.subset ⟨hxb, hxd⟩
    · exact ((hJs.subset hxJ).2 (hstop (hs.1 (Or.inl hxb)))).elim
  obtain ⟨C, e, hCI, hC, he, hbe, hCd, hCQ⟩ :=
    hI.exists_protected_boundary_collar hb hd hbd Q hQ hQI hQb
  have hCO : C ∩ O ⊆ q := by
    rintro x ⟨hxC, hxO⟩
    exact hCQ ⟨hxC, hQs.symm.subset (Or.inl (hLO.symm.subset hxO))⟩
  have hCJ : C ∩ J.space ⊆ q := by
    rintro x ⟨hxC, hxJ⟩
    exact hCQ ⟨hxC, hQs.symm.subset (Or.inr hxJ)⟩
  have hqB : q ⊆ B := fun _ hx => hsB (hs.1 (Or.inl (hb.1 hx)))
  have hqT : q ⊆ T := fun _ hx => hstop (hs.1 (Or.inl (hb.1 hx)))
  have hCS : C ⊆ S := hCI.trans (subset_union_right.trans hinner.subset)
  have hCB : C ⊆ B := by
    intro x hxC
    rcases hcover.symm.subset (hCS hxC) with hxB | hxO
    · exact hxB
    · exact hqB (hCO ⟨hxC, hxO⟩)
  have hCT : C ⊆ T := by
    intro x hxC
    by_contra hxT
    have hxJ : x ∈ J.space := hJs.symm.subset ⟨hCS hxC, hxT⟩
    exact hxT (hqT (hCJ ⟨hxC, hxJ⟩))
  have hsC : s ∩ C = b := by
    apply Subset.antisymm
    · rintro x ⟨hxs, hxC⟩
      rcases hsI.subset ⟨hxs, hCI hxC⟩ with hxb | hxd
      · exact hxb
      · exact hb.1 (hCd.subset ⟨hxC, hxd⟩)
    · intro x hxb
      exact ⟨hs.1 (Or.inl hxb), hC.1 (Or.inl hxb)⟩
  exact hB.excision_of_spherical_boundary_collar hdim hO hs hC hb hc hd he
    hbd hbe hcd hsC hsB hCB hBO hsO hCO
    (subset_union_left.trans hcover.subset)
    (subset_union_right.trans hcover.subset) (union_subset hstop hCT)

end Set
