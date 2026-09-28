import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartner









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1


theorem HasRetainedComponentModel.finitePL_id {U : Set V2}
    (h : HasRetainedComponentModel U) : FinitePiecewiseAffineOn (id : V2 → V2) U := by
  rcases h with h | ⟨n, P, _, hP, hPU, _⟩
  · obtain ⟨_, C, _, _, _, e, ⟨f, ⟨K, hK, hKU, _⟩, _⟩, _⟩ := h
    exact ⟨K, hK, hKU, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  · exact ⟨P.simplicialComplex hP, P.finite_simplicialComplex_faces hP,
      (P.simplicialComplex_space hP).trans hPU,
      (P.simplicialComplex hP).affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩

namespace PolygonalCrossingResolution



theorem double_locus_copy_isFinitePL
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (hL : FinitePiecewiseAffineOn (id : V2 → V2) (doubleLocusOn f K))
    (H : doubleLocusOn f K ≃ₜ doubleLocusOn g D2)
    (hH : ∀ x, (H x : V2) = j ⟨x, x.property.1⟩) : H.IsFinitePL := by
  obtain ⟨J, hJ, hJval⟩ := hPL
  obtain ⟨L, hLf, hLs, _⟩ := hL
  refine ⟨J, ?_, fun x ↦ (hH x).trans (hJval _).symm⟩
  rw [← hLs]
  exact hJ.restrict L hLf (fun _ hx ↦ (hLs ▸ hx).1)



theorem restricted_double_partner_isFinitePL
    {X : Type*} {f : V2 → X} {K : Set V2} (hKS : K ⊆ D2)
    (p : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2) (hp : p.IsFinitePL)
    (hL : FinitePiecewiseAffineOn (id : V2 → V2) (doubleLocusOn f K))
    (q : doubleLocusOn f K ≃ₜ doubleLocusOn f K)
    (hq : ∀ x : doubleLocusOn f K,
      ∃ hx : (x : V2) ∈ doubleLocusOn f D2, (q x : V2) = p ⟨x, hx⟩) :
    q.IsFinitePL := by
  obtain ⟨P, hP, hPval⟩ := hp
  obtain ⟨L, hLf, hLs, _⟩ := hL
  have hsub : L.space ⊆ doubleLocusOn f D2 := by
    intro x hx
    obtain ⟨hxK, y, hyK, hxy, hne⟩ := hLs ▸ hx
    exact ⟨hKS hxK, y, hKS hyK, hxy, hne⟩
  refine ⟨P, hLs ▸ hP.restrict L hLf hsub, ?_⟩
  intro x
  obtain ⟨hx, hval⟩ := hq x
  exact hval.trans (hPval _)



theorem retained_double_locus_finitePL_id
    {X I : Type*} [Finite I] {f : V2 → X} {K : Set V2} (hKS : K ⊆ D2)
    (U : I → Set V2) (mate : I → I)
    (p : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hmodel : ∀ i, HasRetainedComponentModel (U i))
    (hpartner : ∀ x : doubleLocusOn f D2, f x = f (p x))
    (hne : ∀ x : doubleLocusOn f D2, (x : V2) ≠ p x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (p x : V2))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (p x : V2) ∈ U (mate i))
    (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K) :
    FinitePiecewiseAffineOn (id : V2 → V2) (doubleLocusOn f K) := by
  have heq := image_retained_double_locus_eq_paired_components U mate p rfl
    hcover hpartner hne hunique hmate hKS hwhole
  have himage : (Subtype.val : K → V2) ''
      {x : K | ∃ y : K, f x = f y ∧ (x : V2) ≠ y} = doubleLocusOn f K := by
    ext x
    constructor
    · rintro ⟨x, ⟨y, heq, hne⟩, rfl⟩
      exact ⟨x.property, y, y.property, heq, hne⟩
    · rintro ⟨hx, y, hy, heq, hne⟩
      exact ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, heq, hne⟩, rfl⟩
  rw [himage] at heq
  rw [heq]
  exact FinitePiecewiseAffineOn.iUnion
    (fun i : {i // U i ⊆ K ∧ U (mate i) ⊆ K} ↦ (hmodel i.val).finitePL_id)



theorem RetainedSquareMapFacts.exists_finitePL_partner
    {X : Type*} {f g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j) (hK : IsCompact K)
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (hL : FinitePiecewiseAffineOn (id : V2 → V2) (doubleLocusOn f K))
    (p : doubleLocusOn f D2 ≃ₜ doubleLocusOn f D2)
    (hpPL : p.IsFinitePL) (hp : Function.Involutive p)
    (hvalue : ∀ x, f (p x) = f x)
    (hfree : ∀ x, (p x : V2) ≠ x)
    (hrim : ∀ x, (p x : V2) ∈ sphere (0 : V2) 1 ↔ (x : V2) ∈ sphere (0 : V2) 1)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (p x : V2)) :
    ∃ q : doubleLocusOn g D2 ≃ₜ doubleLocusOn g D2,
      q.IsFinitePL ∧ q.symm.IsFinitePL ∧ Function.Involutive q ∧
      (∀ x, g (q x) = g x) ∧ (∀ x, (q x : V2) ≠ x) ∧
      (∀ x, (q x : V2) ∈ sphere (0 : V2) 1 ↔ (x : V2) ∈ sphere (0 : V2) 1) ∧
      (∀ (x : doubleLocusOn g D2) (y : V2), y ∈ D2 →
        g x = g y → (x : V2) ≠ y → y = (q x : V2)) := by
  obtain ⟨q, hq2, hqvalue, hqfree, hqrim, hqunique⟩ :=
    facts.exists_partner hK p hp hvalue hfree hrim hunique
  obtain ⟨H, hH⟩ := facts.exists_double_locus_copy hK
  have hHPL := double_locus_copy_isFinitePL hPL hL H hH
  obtain ⟨r, _, hrval⟩ := exists_restricted_double_partner facts.old_subset p hp hvalue hfree hunique
  have hrPL := restricted_double_partner_isFinitePL facts.old_subset p hpPL hL r hrval
  have heq : q = H.symm.trans (r.trans H) := by
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    obtain ⟨a, rfl⟩ := H.surjective x
    have hkeep (z : doubleLocusOn f K) : g (H z) = f z := by
      rw [hH]
      exact facts.keep _
    have hvalue' : g (H a) = g (H (r a)) := by
      rw [hkeep, hkeep]
      obtain ⟨ha, hval⟩ := hrval a
      rw [hval]
      exact (hvalue ⟨a, ha⟩).symm
    have hne' : (H a : V2) ≠ H (r a) := by
      intro h
      have haeq : a = r a := H.injective (Subtype.ext h)
      obtain ⟨ha, hval⟩ := hrval a
      exact hfree ⟨a, ha⟩ (hval.symm.trans (congrArg Subtype.val haeq).symm)
    have hmate := hqunique (H a) (H (r a)) (H (r a)).property.1 hvalue' hne'
    simpa using hmate.symm
  have hqPL : q.IsFinitePL := heq ▸ hHPL.symm.trans (hrPL.trans hHPL)
  exact ⟨q, hqPL, hqPL.symm, hq2, hqvalue, hqfree, hqrim, hqunique⟩

end PolygonalCrossingResolution
end PoincareConjecture.M76.Dehn
