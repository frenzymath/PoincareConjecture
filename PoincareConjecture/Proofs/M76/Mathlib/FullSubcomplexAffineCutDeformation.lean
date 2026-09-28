import PoincareConjecture.Proofs.M76.Mathlib.FullSubcomplexSuperlevelDeformation
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.AffineLevelSubcomplex

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

open scoped Classical in

theorem exists_full_subcomplex_affine_cut_deformation_mass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces)
    (ell : E →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell) :
    ∃ w : E → ℝ, K.AffineOnFaces w ∧
      (∀ v ∈ K.vertices, w v = if v ∈ L.vertices then 1 else 0) ∧
      (∀ x ∈ L.space, w x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
        ∃ H : C(I × N, E), (∀ z, H z ∈ N) ∧
          (∀ x : N, H (0, x) = (x : E)) ∧
          (∀ x : N, H (1, x) ∈ L.space) ∧
          (∀ (t : I) (x : N), (x : E) ∈ L.space → H (t, x) = (x : E)) ∧
          (∀ (t : I) (x : N), 0 ≤ ell x → 0 ≤ ell (H (t, x))) ∧
          (∀ (t : I) (x : N), ell x = 0 → ell (H (t, x)) = 0) ∧
          ∀ (t : I) (x : N), w (H (t, x)) =
            (1 - (t : ℝ)) * w x + (t : ℝ) := by
  classical
  have hneg : K.RespectsAffineHyperplane (-ell) := by
    intro s hs
    rcases halign s hs with h | h
    · right
      intro x hx
      exact neg_nonneg.mpr (h x hx)
    · left
      intro x hx
      exact neg_nonpos.mpr (h x hx)
  let B := K.affineHalfspaceSubcomplex {-ell}
  let Z := K.affineZeroSubcomplex ell
  have hBK : B ≤ K := fun _ hs => hs.1
  have hZK : Z ≤ K := fun _ hs => hs.1
  have hBs : B.space = K.space ∩ {x | 0 ≤ ell x} := by
    change (K.affineHalfspaceSubcomplex {-ell}).space = _
    rw [K.affineHalfspaceSubcomplex_space {-ell}
      (by intro a ha; simpa only [Finset.mem_singleton.mp ha] using hneg)]
    simp only [Finset.mem_singleton, forall_eq, AffineMap.coe_neg, Pi.neg_apply, neg_nonpos]
  have hZs : Z.space = K.space ∩ {x | ell x = 0} :=
    K.affineZeroSubcomplex_space ell halign
  obtain ⟨w, hw, hwv, hwL, hdeform⟩ :=
    K.exists_full_subcomplex_superlevel_deformation_preserving_subcomplexes_mass L hK hLK hfull
  refine ⟨w, hw, hwv, hwL, ?_⟩
  intro c hc hc1
  obtain ⟨_, _, _, _, _, _, H, hHN, hH0, hH1, hfix, hpreserve, hmass⟩ := hdeform c hc hc1
  refine ⟨H, hHN, hH0, hH1, hfix, ?_, ?_, hmass⟩
  · intro t x hx
    have hxB : (x : E) ∈ B.space := hBs.symm ▸ ⟨x.property.1, hx⟩
    have hHB := hpreserve B hBK t x hxB
    rw [hBs] at hHB
    exact hHB.2
  · intro t x hx
    have hxZ : (x : E) ∈ Z.space := hZs.symm ▸ ⟨x.property.1, hx⟩
    have hHZ := hpreserve Z hZK t x hxZ
    rw [hZs] at hHZ
    exact hHZ.2

open scoped Classical in

theorem exists_full_subcomplex_affine_cut_deformation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces)
    (ell : E →ᵃ[ℝ] ℝ) (halign : K.RespectsAffineHyperplane ell) :
    ∃ w : E → ℝ, K.AffineOnFaces w ∧
      (∀ v ∈ K.vertices, w v = if v ∈ L.vertices then 1 else 0) ∧
      (∀ x ∈ L.space, w x = 1) ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        let N : Set E := {x | x ∈ K.space ∧ c ≤ w x}
        ∃ H : C(I × N, E), (∀ z, H z ∈ N) ∧
          (∀ x : N, H (0, x) = (x : E)) ∧
          (∀ x : N, H (1, x) ∈ L.space) ∧
          (∀ (t : I) (x : N), (x : E) ∈ L.space → H (t, x) = (x : E)) ∧
          (∀ (t : I) (x : N), 0 ≤ ell x → 0 ≤ ell (H (t, x))) ∧
          ∀ (t : I) (x : N), ell x = 0 → ell (H (t, x)) = 0 := by
  obtain ⟨w, hw, hwv, hwL, hdeform⟩ :=
    K.exists_full_subcomplex_affine_cut_deformation_mass L hK hLK hfull ell halign
  refine ⟨w, hw, hwv, hwL, ?_⟩
  intro c hc hc1
  obtain ⟨H, hHN, hH0, hH1, hfix, hpos, hzero, _⟩ := hdeform c hc hc1
  exact ⟨H, hHN, hH0, hH1, hfix, hpos, hzero⟩

end Geometry.SimplicialComplex
