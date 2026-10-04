import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Spheres.BoundedRegionSphericalExcision
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.BoundedRegionBoundaryCollar

/-!
# Complementary ball from nested certified spherical regions

Protect the entire outer exterior while taking a boundary collar
inside the inner exterior. Spherical covering forces this collar
into the outer ball. The resulting exact incidences feed the
finite PL compression and excision construction.
See Alexander 1924, p. 7, Hudson 1969, Lemma 2.14, pp. 60--61
and M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Both sides of two nested capped spheres construct the
remaining finite PL ball by an actual protected collar and
compression. The collar and all its incidence equations are
derived from the certified sides. See Alexander p. 7,
Hudson pp. 60--61 and M76 derivation 247. -/
theorem IsFinitePLBallPair.excision_of_nested_spherical_balls
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
    (hIsphere : I ⊆ frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (hBtop : B ⊆ interior D ×ˢ {(1 : ℝ)}) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (B \ s)) (b ∪ c) := by
  have hOcopy := hO
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKO, _⟩, _⟩, _⟩ := hOcopy
  have hKI : K.space ⊆ I := hKO.subset.trans hOI
  have hKb : K.space ∩ b ⊆ q := by
    rintro x ⟨hxK, hxb⟩
    have hxd : x ∈ d := hsO.subset ⟨hs.1 (Or.inl hxb), hKO.subset hxK⟩
    exact hbd.subset ⟨hxb, hxd⟩
  obtain ⟨C, e, hCI, hC, he, hbe, hCd, hCK⟩ :=
    hI.exists_protected_boundary_collar hb hd hbd K hK hKI hKb
  have hCO : C ∩ O ⊆ q := by
    simpa only [hKO] using hCK
  have hqB : q ⊆ B := fun _ hx => hsB (hs.1 (Or.inl (hb.1 hx)))
  have hCB : C ⊆ B := by
    intro x hxC
    rcases hcover.symm.subset (hIsphere (hCI hxC)) with hxB | hxO
    · exact hxB
    · exact hqB (hCO ⟨hxC, hxO⟩)
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
    (subset_union_right.trans hcover.subset)
    ((union_subset hsB hCB).trans hBtop)

end Set
