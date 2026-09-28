import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineSectionFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsCompact.isFinitePLBallPair_affine_section {s : Set E}
    (hs : IsCompact s) (hcv : Convex ℝ s) (L : E →ₗ[ℝ] ℝ)
    (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F) (hleft : Function.LeftInverse r a)
    (hright : LeftInvOn a r {x | L x = 1}) (ha : ∀ y, L (a y) = 1)
    (hne : (interior s ∩ {x | L x = 1}).Nonempty)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hspace : K.space = s ∩ {x | L x = 1}) :
    IsFinitePLBallPair F (s ∩ {x | L x = 1}) (frontier s ∩ {x | L x = 1}) := by
  let T := s ∩ {x | L x = 1}
  let C := a ⁻¹' s
  have hrC : r '' T = C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a (r x) ∈ s
      rw [hright hx.2]
      exact hx.1
    · intro hy
      exact ⟨a y, ⟨hy, ha y⟩, hleft y⟩
  have hT : IsCompact T := hs.inter_right
    (isClosed_eq L.continuous_of_finiteDimensional continuous_const)
  have hC : IsCompact C := hrC ▸ hT.image r.continuous
  have hCcv : Convex ℝ C := hcv.affine_preimage a.toAffineMap
  obtain ⟨w, hwS, hwL⟩ := hne
  have hrange : ∃ y, a y ∈ interior s :=
    ⟨r w, by rw [hright hwL]; exact hwS⟩
  have hCne : (interior C).Nonempty := by
    obtain ⟨y, hy⟩ := hrange
    exact ⟨y, preimage_interior_subset_interior_preimage a.continuous hy⟩
  have hf : FinitePiecewiseAffineOn r T :=
    ⟨K, hK, hspace, K.affineOnFaces_affine r⟩
  have hinj : InjOn r T := fun x hx y hy hxy => by
    have h := congrArg a hxy
    rwa [hright hx.2, hright hy.2] at h
  obtain ⟨e, he, hval⟩ := hf.exists_homeomorph_image hinj
  let G := (Homeomorph.setCongr (rfl : T = T)).trans (e.trans (Homeomorph.setCongr hrC))
  have hGval (x : T) : (G x : F) = r x := hval x
  refine ⟨fun x hx => ⟨hs.isClosed.frontier_subset hx.1, hx.2⟩,
    C, hC, hCcv, hCne, G, he.setCongr rfl hrC, fun x => ?_⟩
  rw [hGval, a.frontier_preimage_convex hs.isClosed hcv hrange]
  change ((x : E) ∈ frontier s ∧ L (x : E) = 1) ↔ a (r x) ∈ frontier s
  rw [hright x.property.2]
  exact and_iff_left x.property.2

end Set
