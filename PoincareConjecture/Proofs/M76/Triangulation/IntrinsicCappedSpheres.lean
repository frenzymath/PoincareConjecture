import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicPlanarCap
import PoincareConjecture.Proofs.M76.Triangulation.PLSpherePolygonCut
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Polygon

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Finite ι] [Nonempty ι]

theorem exists_intrinsic_capped_spheres
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (q : E) (hpair : Pairwise (fun i j =>
      (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}))
    (S : Set E) (hsection : S ∩ {x | A x = 0} = ⋃ i, (P i).boundary ℝ)
    (hoff : ∃ x ∈ S, A x ≠ 0)
    {C : Set F} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hne : (interior C).Nonempty) (hdimC : Module.finrank ℝ F = 3)
    (e : S ≃ₜ frontier C) (he : e.IsFinitePL) :
    ∃ (j : ι) (d s₀ s₁ : Set E) (N : SimplicialComplex ℝ E),
      IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s₀ ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s₁ ((P j).boundary ℝ) ∧
      d ⊆ {x | A x = 0} ∧ d ∩ S = (P j).boundary ℝ ∧
      s₀ ∪ s₁ = S ∧ s₀ ∩ s₁ = (P j).boundary ℝ ∧
      s₀ ∩ d = (P j).boundary ℝ ∧ s₁ ∩ d = (P j).boundary ℝ ∧
      N.faces.Finite ∧ S ∩ {x | A x = 0} = (P j).boundary ℝ ∪ N.space ∧
      d ∩ N.space ⊆ {q} ∧
      N.space = ⋃ i : {i : ι // i ≠ j}, (P i.val).boundary ℝ ∧
      ∃ (e₀ : (s₀ ∪ d : Set E) ≃ₜ frontier (halfBall 1))
        (e₁ : (s₁ ∪ d : Set E) ≃ₜ frontier (halfBall 1)), e₀.IsFinitePL ∧ e₁.IsFinitePL := by
  obtain ⟨j, d, N, hd, hdplane, hcap, hN, hsplit, hdN, hfamily⟩ :=
    exists_intrinsic_plane_cap hdim A hA n P hP q hpair S hsection
  have hPS : (P j).boundary ℝ ⊆ S := hcap.symm.subset.trans inter_subset_right
  obtain ⟨x, hxS, hxA⟩ := hoff
  have hxP : x ∉ (P j).boundary ℝ := fun hx => hxA (hdplane (hd.1 hx))
  obtain ⟨s₀, s₁, hs₀, hs₁, hunion, hinter, _⟩ :=
    he.exists_polygon_cut hC hcv hne hdimC (P j) (hP j).2 (hP j).1 hPS ⟨x, hxS⟩ hxP
  have hsS : s₀ ⊆ S := subset_union_left.trans hunion.subset
  have hs'S : s₁ ⊆ S := subset_union_right.trans hunion.subset
  have hs₀d : s₀ ∩ d = (P j).boundary ℝ := by
    apply Subset.antisymm
    · exact fun _ hx => hcap.subset ⟨hx.2, hsS hx.1⟩
    · exact fun _ hx => ⟨hs₀.1 hx, hd.1 hx⟩
  have hs₁d : s₁ ∩ d = (P j).boundary ℝ := by
    apply Subset.antisymm
    · exact fun _ hx => hcap.subset ⟨hx.2, hs'S hx.1⟩
    · exact fun _ hx => ⟨hs₁.1 hx, hd.1 hx⟩
  obtain ⟨e₀, he₀, _⟩ := hs₀.exists_sphere_model_of_disk_union hd hs₀d
  obtain ⟨e₁, he₁, _⟩ := hs₁.exists_sphere_model_of_disk_union hd hs₁d
  exact ⟨j, d, s₀, s₁, N, hd, hs₀, hs₁, hdplane, hcap, hunion, hinter,
    hs₀d, hs₁d, hN, hsplit, hdN, hfamily, e₀, e₁, he₀, he₁⟩

end Polygon
