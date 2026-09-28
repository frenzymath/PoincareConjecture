import PoincareConjecture.Proofs.M76.Mathlib.OrientedFiniteHeightCutBoxes
import PoincareConjecture.Proofs.M76.Mathlib.PlanarDiskCutOrientation












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}






theorem exists_inward_oriented_affine_height_cut_boxes
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (S : Set E) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ E = 3) (c : ℝ)
    (hsection : P.boundary ℝ = S ∩ {x | A x = c})
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hdplane : d ⊆ {x | A x = c})
    (W : Fin (n + 3) → Set E) {R : ℝ} (hR : 0 < R)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hf : ∀ i, f i 0 = P.edgeCut t i ∧ f i '' box R ⊆ W i ∧
      (∀ x, A (f i x) = c + x.1.1) ∧
      ∀ x ∈ box R, f i x ∈ S ↔ x.2 = 0)
    (hdisj : Pairwise fun i j => Disjoint (f i '' box R) (f j '' box R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (g : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
      r ∈ Ioo 0 ε ∧ r ≤ R ∧
      (∀ i,
        g i 0 = P.edgeCut t i ∧
        (∀ a, g i '' box a = f i '' box a) ∧
        g i '' box r ⊆ W i ∧
        P.edgeCut t i ∈ interior (g i '' box r) ∧
        (∀ x, A (g i x) = c + x.1.1) ∧
        (∀ x ∈ box r, g i x ∈ S ↔ x.2 = 0) ∧
        (∀ x ∈ box r,
          (g i x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
          (g i x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
            x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0)) ∧
        ∀ x ∈ box r, x.1.1 = 0 → (g i x ∈ d ↔ 0 ≤ x.2)) ∧
      Pairwise fun i j => Disjoint (g i '' box r) (g j '' box r) := by
  classical
  obtain ⟨r, k, hr, hrR, hk, hkdisj⟩ :=
    P.exists_oriented_affine_height_cut_boxes hP hinj t ht S A c hsection W hR f hf hdisj hε
  have hd' : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c}) := hsection ▸ hd
  have hlocal (i : Fin (n + 3)) :
      ∃ g : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
        (g = k i ∨ g = transverseReflection.toContinuousAffineEquiv.trans (k i)) ∧
        g 0 = k i 0 ∧ (∀ a, g '' box a = k i '' box a) ∧
        (∀ x, A (g x) = c + x.1.1) ∧
        (∀ x ∈ box r, g x ∈ S ↔ x.2 = 0) ∧
        ∀ x ∈ box r, x.1.1 = 0 → (g x ∈ d ↔ 0 ≤ x.2) := by
    obtain ⟨_, _, _, _, _, hheight, hsurface, _⟩ := hk i
    exact (k i).exists_positive_transverse_planar_cut hr.1 A hA hdim
      hheight hsurface hd' hdplane
  choose g hgchoice hgzero hgimage hgheight hgsurface hginward using hlocal
  refine ⟨r, g, hr, hrR, ?_, ?_⟩
  · intro i
    obtain ⟨_, hkzero, hkimage, hkW, hkinterior, _, _, hkarcs⟩ := hk i
    refine ⟨(hgzero i).trans hkzero, fun a => (hgimage i a).trans (hkimage a),
      ?_, ?_, hgheight i, hgsurface i, ?_, hginward i⟩
    · rw [hgimage i r]
      exact hkW
    · rw [hgimage i r]
      exact hkinterior
    · intro x hx
      rcases hgchoice i with hsame | hreflect
      · rw [hsame]
        exact hkarcs x hx
      · rw [hreflect]
        change
          (k i (transverseReflection x) ∈ P.cutArc t i ↔
            x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
          (k i (transverseReflection x) ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
            x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0)
        simpa only [transverseReflection_apply, neg_eq_zero] using
          hkarcs (transverseReflection x) ((transverseReflection_mem_box r x).mpr hx)
  · intro i j hij
    rw [hgimage i r, hgimage j r]
    exact hkdisj hij

end Polygon
