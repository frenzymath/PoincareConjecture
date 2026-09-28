import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereFirstCapExterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineCylinderExterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem IsFinitePL.exists_first_height_cap_ball_with_exterior
    {s : Set E} {T : Set F} {e : s ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hTne : (interior T).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hCcv : Convex ℝ C) (hKC : K.space = C)
    {p : E} (hpC : p ∈ interior C) (hps : p ∈ s)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hpA : A p = 0)
    (hmin : ∀ x ∈ s, 0 ≤ A x) (hzero : s ∩ {x | A x = 0} = {p})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β ∈ Ioo (0 : ℝ) ε, ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = β}) ∧
      (∀ x ∈ d, A x = β) ∧ d ∩ s = s ∩ {x | A x = β} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {p} d)
        (d ∪ (s ∩ {x | A x ≤ β})) ∧
      convexJoin ℝ {p} d ∩ s = s ∩ {x | A x ≤ β} ∧
      convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc 0 β} ∧
      d ⊆ interior C ∧ convexJoin ℝ {p} d ⊆ interior C ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior (convexJoin ℝ {p} d) ×ˢ {1})
        ((d ∪ (s ∩ {x | A x ≤ β})) ×ˢ {(1 : ℝ)}) := by
  classical
  let τ : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hτp : τ p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hτzero : τ.symm 0 = p := by rw [← hτp, τ.symm_apply_apply]
  have hheight (x : E) : A.linear (τ x) = A x := by
    have h := A.linearMap_vsub x p
    change A.linear (x - p) = A x - A p at h
    rw [hpA, sub_zero] at h
    change A.linear (-p + x) = A x
    simpa only [sub_eq_add_neg, add_comm] using h
  let s' := τ '' s
  let C' := τ '' C
  let e' : s' ≃ₜ frontier T := (τ.toHomeomorph.image s).symm.trans e
  have he' : e'.IsFinitePL := by
    obtain ⟨f, hf, hfe⟩ := he
    refine ⟨f ∘ τ.symm, hf.precomp_affineEquiv τ.symm, ?_⟩
    intro x
    exact hfe ((τ.toHomeomorph.image s).symm x)
  let hτK := K.affineOnFaces_affine τ.toContinuousAffineMap
  let J := hτK.embeddedImage τ.injective.injOn
  have hJ : J.faces.Finite := hτK.embeddedImage_finite τ.injective.injOn hK
  have hJC : J.space = C' := by
    rw [hτK.embeddedImage_space τ.injective.injOn, hKC]
    rfl
  have hC' : IsCompact C' := hC.image τ.continuous
  have hC'cv : Convex ℝ C' := hCcv.affine_image τ.toAffineEquiv.toAffineMap
  have hC'0 : (0 : E) ∈ interior C' := by
    exact (τ.toHomeomorph.image_interior C).subset ⟨p, hpC, hτp⟩
  have h0s' : (0 : E) ∈ s' := ⟨p, hps, hτp⟩
  have hmin' : ∀ x ∈ s', 0 ≤ A.linear x := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hheight]
    exact hmin x hx
  have hsection (U : Set ℝ) :
      τ '' (s ∩ A ⁻¹' U) = s' ∩ A.linear ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      change A.linear (τ x) ∈ U
      rw [hheight]
      exact hx.2
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      change A x ∈ U
      rw [← hheight]
      exact hy
  have hzero' : s' ∩ {x | A.linear x = 0} = {0} := by
    have hsec : τ '' (s ∩ {x | A x = 0}) = s' ∩ {x | A.linear x = 0} :=
      hsection {0}
    rw [← hsec, hzero, image_singleton, hτp]
  have hback (U : Set E) : τ.symm '' (τ '' U) = U := by
    rw [image_image]
    simp only [τ.symm_apply_apply, image_id']
  have hsectionback (U : Set ℝ) :
      τ.symm '' (s' ∩ A.linear ⁻¹' U) = s ∩ A ⁻¹' U := by
    rw [← hsection U, hback]
  have hCback : τ.symm '' C' = C := hback C
  have hCintback : τ.symm '' interior C' = interior C :=
    (τ.symm.toHomeomorph.image_interior C').trans (congrArg interior hCback)
  obtain ⟨β, hβ, d', hd', hd'plane, hd'contact, hball', hcontact', hband', hd'C,
      hcone'C, hexterior'⟩ :=
    he'.exists_first_height_cap_ball_with_exterior_zero hT hTcv hTne hdimF hdimE
      J hJ hC' hC'cv hJC hC'0 h0s' A.linear hA hmin' hzero' hε
  let d := τ.symm '' d'
  have hrimback : τ.symm '' (s' ∩ {x | A.linear x = β}) = s ∩ {x | A x = β} :=
    hsectionback {β}
  have hsubback : τ.symm '' (s' ∩ {x | A.linear x ≤ β}) = s ∩ {x | A x ≤ β} :=
    hsectionback (Iic β)
  have hconeback : τ.symm '' convexJoin ℝ {0} d' = convexJoin ℝ {p} d := by
    change τ.symm.toAffineEquiv.toAffineMap '' convexJoin ℝ {0} d' = _
    rw [AffineMap.image_convexJoin, image_singleton]
    change convexJoin ℝ {τ.symm 0} d = convexJoin ℝ {p} d
    rw [hτzero]
  have hboundaryback : τ.symm '' (d' ∪ (s' ∩ {x | A.linear x ≤ β})) =
      d ∪ (s ∩ {x | A x ≤ β}) := by
    rw [image_union, hsubback]
  have hd := hd'.affine_image τ.symm.toContinuousAffineMap τ.symm.injective.injOn
  change IsFinitePLBallPair (ℝ × ℝ) d (τ.symm '' (s' ∩ {x | A.linear x = β})) at hd
  rw [hrimback] at hd
  have hdplane : ∀ x ∈ d, A x = β := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hheight, τ.apply_symm_apply]
    exact hd'plane x hx
  have hdcontact : d ∩ s = s ∩ {x | A x = β} := by
    have h := congrArg (fun U : Set E => τ.symm '' U) hd'contact
    rw [image_inter τ.symm.injective, hback s, hrimback] at h
    exact h
  have hball := hball'.affine_image τ.symm.toContinuousAffineMap τ.symm.injective.injOn
  change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (τ.symm '' convexJoin ℝ {0} d')
    (τ.symm '' (d' ∪ (s' ∩ {x | A.linear x ≤ β}))) at hball
  rw [hconeback, hboundaryback] at hball
  have hcontact : convexJoin ℝ {p} d ∩ s = s ∩ {x | A x ≤ β} := by
    have h := congrArg (fun U : Set E => τ.symm '' U) hcontact'
    rw [image_inter τ.symm.injective, hconeback, hback s, hsubback] at h
    exact h
  have hband : convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc 0 β} := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hconeback.symm.subset hy
    change A (τ.symm x) ∈ Icc 0 β
    rw [← hheight, τ.apply_symm_apply]
    exact hband' hx
  have hdC : d ⊆ interior C := by
    rw [← hCintback]
    exact image_mono hd'C
  have hconeC : convexJoin ℝ {p} d ⊆ interior C := by
    rw [← hconeback, ← hCintback]
    exact image_mono hcone'C
  have hexterior := hexterior'.affine_cylinderExterior τ.symm
  rw [hCback, hconeback, hboundaryback] at hexterior
  exact ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hband, hdC, hconeC,
    hexterior⟩

end Homeomorph
