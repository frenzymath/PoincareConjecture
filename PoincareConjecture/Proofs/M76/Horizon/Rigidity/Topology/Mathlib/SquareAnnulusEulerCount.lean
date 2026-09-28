import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SquareAnnulusSubdivision
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceTriangulationCount

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PLAnnularStrip

theorem convex_stripRegion (L d : ℝ) (i : Fin 4) : Convex ℝ (stripRegion L d i) := by
  have hc : Convex ℝ (trapezoid L d) := by
    let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
    let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    have hc := ((convex_Icc (-d) d).affine_preimage y.toAffineMap).inter
      (((convex_Ici (0 : ℝ)).affine_preimage (x - y).toAffineMap).inter
        ((convex_Iic L).affine_preimage (x + y).toAffineMap))
    convert hc using 1 <;> try rfl
    ext p
    simp only [trapezoid, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici, mem_Iic]
    change (p.2 ∈ Icc (-d) d ∧ p.2 ≤ p.1 ∧ p.1 ≤ L - p.2) ↔
      p.2 ∈ Icc (-d) d ∧ 0 ≤ p.1 - p.2 ∧ p.1 + p.2 ≤ L
    constructor <;> rintro ⟨h₀, h₁, h₂⟩ <;> exact ⟨h₀, by linarith, by linarith⟩
  rw [← stripRotation_image]
  exact hc.affine_image (stripRotation L i).toAffineMap

theorem strip_count (L d : ℝ) (hd : 0 ≤ d) (hwidth : 4 * d < L) (i : Fin 4)
    (D : SimplicialComplex ℝ (ℝ × ℝ)) (hD : D.space = stripRegion L d i)
    (hDf : D.faces.Finite) : D.surfaceEulerCount = 1 := by
  apply D.surfaceEulerCount_eq_one_of_convex_low_dimension hDf
    (hD ▸ convex_stripRegion L d i) ?_ (⊤ : AffineSubspace ℝ (ℝ × ℝ))
    (by intro x hx; trivial)
    (by rw [AffineSubspace.direction_top]
        rw [finrank_top, Module.finrank_prod]
        norm_num)
  rw [hD]
  have hreg : (stripRegion L d i).Nonempty := by
    rw [← stripRotation_image]
    rw [← stripMap_image hwidth, ← image_comp]
    have hL : 0 ≤ L := by linarith
    obtain ⟨x, hx⟩ : (rectangle L d).Nonempty := by
      refine ⟨(0, 0), ?_⟩
      simp only [rectangle, mem_prod, mem_Icc]
      exact ⟨⟨le_rfl, hL⟩, ⟨by linarith, hd⟩⟩
    exact Set.Nonempty.image (stripRotation L i ∘ stripMap L) ⟨x, hx⟩
  exact hD ▸ hreg

theorem segment_image_count {a b : ℝ} (hab : a ≤ b)
    (g : ℝ →ᵃ[ℝ] (ℝ × ℝ)) (D : SimplicialComplex ℝ (ℝ × ℝ))
    (hD : D.space = g '' Icc a b) (hDf : D.faces.Finite) :
    D.surfaceEulerCount = 1 := by
  apply D.surfaceEulerCount_eq_one_of_convex_low_dimension hDf
    (hD ▸ (convex_Icc a b).affine_image g) ?_ (⊤ : AffineSubspace ℝ (ℝ × ℝ))
    (by intro x hx; trivial)
    (by rw [AffineSubspace.direction_top, finrank_top, Module.finrank_prod]; norm_num)
  rw [hD]
  exact ⟨g a, ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩

theorem inf_faces_eq_empty_of_disjoint_space
    {A B : SimplicialComplex ℝ (ℝ × ℝ)}
    (hdisj : Disjoint A.space B.space) : (A ⊓ B).faces = ∅ := by
  ext s
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := (A ⊓ B).nonempty_of_mem_faces hs
    have hpA : p ∈ A.space := A.convexHull_subset_space hs.1
      (subset_convexHull ℝ _ hp)
    have hpB : p ∈ B.space := B.convexHull_subset_space hs.2
      (subset_convexHull ℝ _ hp)
    exact (Set.disjoint_left.mp hdisj) hpA hpB
  · intro hs
    exact hs.elim

theorem exists_squareAnnulus_count {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ (R : SimplicialComplex ℝ (ℝ × ℝ))
      (D : Fin 4 → SimplicialComplex ℝ (ℝ × ℝ))
      (U₀₁ U₂₃ W K : SimplicialComplex ℝ (ℝ × ℝ)),
      R.faces.Finite ∧
      (∀ i, (D i).faces.Finite ∧ (D i).space = stripRegion L d i ∧ D i ≤ R) ∧
      U₀₁.faces = (D 0).faces ∪ (D 1).faces ∧
      U₂₃.faces = (D 2).faces ∪ (D 3).faces ∧
      W.faces = ((D 0 ⊓ D 3).faces ∪ (D 1 ⊓ D 2).faces) ∧
      K.faces = U₀₁.faces ∪ U₂₃.faces ∧
      K.space = squareAnnulus L d ∧ K.surfaceEulerCount = 0 := by
  obtain ⟨R, D, U₀₁, U₂₃, W, K, hR, hD, hU₀₁, hU₂₃, hW, hK, hKs⟩ :=
    exists_squareAnnulus_common_subdivision hd hwidth
  have hstrip (i : Fin 4) : (D i).surfaceEulerCount = 1 :=
    strip_count L d hd.le hwidth i (D i) (hD i).2.1 (hD i).1
  have hinter (i j : Fin 4) (hij : 2 * d < L)
      (g : ℝ →ᵃ[ℝ] (ℝ × ℝ))
      (hg : stripRegion L d i ∩ stripRegion L d j =
        g '' Icc (-d) d) :
      (D i ⊓ D j).surfaceEulerCount = 1 := by
    have hspace : (D i ⊓ D j).space = g '' Icc (-d) d := by
      rw [space_inf_eq_inter_of_le R (D i) (D j) (hD i).2.2 (hD j).2.2,
        (hD i).2.1, (hD j).2.1, hg]
    exact segment_image_count (by linarith [hd]) g
      (D i ⊓ D j) hspace (hR.subset (le_trans inf_le_left (hD i).2.2))
  let g₀₁ : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
    ((ContinuousAffineMap.const ℝ ℝ L - ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.id ℝ ℝ)).toAffineMap
  let g₂₃ : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
    ((ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.const ℝ ℝ L - ContinuousAffineMap.id ℝ ℝ)).toAffineMap
  let g₀₃ : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
    ((ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.id ℝ ℝ)).toAffineMap
  let g₁₂ : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
    ((ContinuousAffineMap.const ℝ ℝ L - ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.const ℝ ℝ L - ContinuousAffineMap.id ℝ ℝ)).toAffineMap
  have hg₀₁ : (g₀₁ : ℝ → ℝ × ℝ) = fun t => (L - t, t) := by
    funext t
    rfl
  have hg₂₃ : (g₂₃ : ℝ → ℝ × ℝ) = fun t => (t, L - t) := by
    funext t
    rfl
  have hg₀₃ : (g₀₃ : ℝ → ℝ × ℝ) = fun t => (t, t) := by
    funext t
    rfl
  have hg₁₂ : (g₁₂ : ℝ → ℝ × ℝ) = fun t => (L - t, L - t) := by
    funext t
    rfl
  have h₀₁ := hinter 0 1 (by linarith [hwidth]) g₀₁ (by
    rw [hg₀₁]
    simpa [stripRegion] using trapezoid_inter_rightStrip (by linarith [hwidth]))
  have h₂₃ := hinter 2 3 (by linarith [hwidth]) g₂₃ (by
    rw [hg₂₃]
    simpa [stripRegion] using topStrip_inter_leftStrip (by linarith [hwidth]))
  have h₀₃ := hinter 0 3 (by linarith [hwidth]) g₀₃ (by
    rw [hg₀₃]
    simpa [stripRegion] using trapezoid_inter_leftStrip (by linarith [hwidth]))
  have h₁₂ := hinter 1 2 (by linarith [hwidth]) g₁₂ (by
    rw [hg₁₂]
    simpa [stripRegion, inter_comm] using topStrip_inter_rightStrip (L := L) (d := d) (by linarith [hwidth]))
  have hempty (i j : Fin 4) (hij : Disjoint (stripRegion L d i) (stripRegion L d j)) :
      (D i ⊓ D j).faces = ∅ := by
    apply inf_faces_eq_empty_of_disjoint_space
    rw [(hD i).2.1, (hD j).2.1]
    exact hij
  have hdisj₀₂ := hempty 0 2 (by
    simpa [stripRegion] using disjoint_trapezoid_topStrip (by linarith [hwidth]))
  have hdisj₁₃ := hempty 1 3 (by
    simpa [stripRegion] using disjoint_rightStrip_leftStrip (by linarith [hwidth]))
  have hdisjW : ((D 0 ⊓ D 3) ⊓ (D 1 ⊓ D 2)).faces = ∅ := by
    ext s
    constructor
    · intro hs
      have hs02 : s ∈ (D 0 ⊓ D 2).faces := ⟨hs.1.1, hs.2.2⟩
      rw [hdisj₀₂] at hs02
      exact hs02.elim
    · intro hs
      exact hs.elim
  refine ⟨R, D, U₀₁, U₂₃, W, K, hR, hD, hU₀₁, hU₂₃, hW, hK, hKs, ?_⟩
  exact surfaceEulerCount_four_strip_cover_eq_zero K (D 0) (D 1) (D 2) (D 3)
    U₀₁ U₂₃ W (hD 0).1 (hD 1).1 (hD 2).1 (hD 3).1 hU₀₁ hU₂₃ hK hW
    (hstrip 0) (hstrip 1) (hstrip 2) (hstrip 3) h₀₁ h₂₃ h₀₃ h₁₂ hdisj₀₂ hdisj₁₃ hdisjW

theorem surfaceEulerCount_eq_zero_of_space_eq_squareAnnulus
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite)
    (hspace : K.space = squareAnnulus L d) : K.surfaceEulerCount = 0 := by
  obtain ⟨_, D, U₀₁, U₂₃, _, K₀, hR, hD, hU₀₁, hU₂₃, _, hK₀faces,
    hK₀space, hK₀count⟩ :=
    exists_squareAnnulus_count hd hwidth
  have hU₀₁finite : U₀₁.faces.Finite := hU₀₁ ▸ (hD 0).1.union (hD 1).1
  have hU₂₃finite : U₂₃.faces.Finite := hU₂₃ ▸ (hD 2).1.union (hD 3).1
  have hK₀finite : K₀.faces.Finite := hK₀faces ▸ hU₀₁finite.union hU₂₃finite
  have hdim (J : SimplicialComplex ℝ (ℝ × ℝ)) (hJ : J.faces.Finite) :
      ∀ s ∈ J.faces, s.card ≤ 3 := by
    intro s hs
    refine Geometry.SimplicialComplex.face_card_le_of_finite_affine_cover J
      ({(⊤ : AffineSubspace ℝ (ℝ × ℝ))} :
        Finset (AffineSubspace ℝ (ℝ × ℝ))) ?_ ?_ hs
    · intro A hA
      have hAtop : A = ⊤ := Finset.mem_singleton.mp hA
      subst A
      rw [AffineSubspace.direction_top, finrank_top]
      simp [Module.finrank_prod]
    · intro x hx
      exact ⟨⊤, Finset.mem_singleton_self _, by simp⟩
  have hcount := Geometry.SimplicialComplex.surfaceEulerCount_eq_of_space_eq
    K K₀ hK hK₀finite (hdim K hK) (hdim K₀ hK₀finite)
      (hspace.trans hK₀space.symm)
  exact hcount.trans hK₀count

end PLAnnularStrip
