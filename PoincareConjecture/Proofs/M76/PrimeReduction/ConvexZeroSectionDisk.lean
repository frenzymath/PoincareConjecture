import PoincareConjecture.Proofs.M76.Mathlib.ConvexSectionBallPair
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem isFinitePLBallPair_convex_zero_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s) (hspace : K.space = s)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hne : ∃ x ∈ interior s, A x = 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    IsFinitePLBallPair F (s ∩ {x | A x = 0}) (frontier s ∩ {x | A x = 0}) := by
  classical
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_triangulation_inter_halfspaces hK {A, -A}
  have hsection : J.space = s ∩ {x | A x = 0} := by
    rw [hJs, hspace]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq, AffineMap.coe_neg, Pi.neg_apply]
    exact and_congr_right (fun _ => ⟨fun h => le_antisymm h.1 (neg_nonpos.mp h.2),
      fun h => by simp [h]⟩)
  obtain ⟨a, r, hleft, hright, ha⟩ := A.exists_zeroLevel_coordinates hA hdim
  let T := s ∩ {x | A x = 0}
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
    (isClosed_eq A.continuous_of_finiteDimensional continuous_const)
  have hC : IsCompact C := hrC ▸ hT.image r.continuous
  obtain ⟨w, hw, hAw⟩ := hne
  have hrange : ∃ y, a y ∈ interior s :=
    ⟨r w, by rw [hright hAw]; exact hw⟩
  have hCne : (interior C).Nonempty := by
    obtain ⟨y, hy⟩ := hrange
    exact ⟨y, preimage_interior_subset_interior_preimage a.continuous hy⟩
  have hf : FinitePiecewiseAffineOn r T :=
    ⟨J, hJ, hsection, J.affineOnFaces_affine r⟩
  have hinj : InjOn r T := by
    intro x hx y hy hxy
    have h := congrArg a hxy
    rwa [hright hx.2, hright hy.2] at h
  obtain ⟨e, he, hval⟩ := hf.exists_homeomorph_image hinj
  let G := e.trans (Homeomorph.setCongr hrC)
  have hGval (x : T) : (G x : F) = r x := hval x
  refine ⟨fun x hx => ⟨hs.isClosed.frontier_subset hx.1, hx.2⟩,
    C, hC, hcv.affine_preimage a.toAffineMap, hCne, G,
    he.setCongr rfl hrC, ?_⟩
  intro x
  rw [hGval, a.frontier_preimage_convex hs.isClosed hcv hrange]
  change ((x : E) ∈ frontier s ∧ A (x : E) = 0) ↔ a (r x) ∈ frontier s
  rw [hright x.property.2]
  exact and_iff_left x.property.2

end Geometry.SimplicialComplex
