import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

local notation "I" => Icc (0 : ℝ) 1



theorem IsFinitePL.exists_boundary_normalized_product
    {A : Set E} {T B : Set F}
    {C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ T} (hC : C.IsFinitePL)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKs : K.space = A)
    (b : A ≃ₜ B)
    (hb : ∀ x : A, (C ⟨((x : E), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F) = b x) :
    ∃ D : (B ×ˢ I : Set (F × ℝ)) ≃ₜ T,
      D.IsFinitePL ∧
      (∀ x : B, (D ⟨((x : F), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F) = x) ∧
      (∀ (x : A) (r : I),
        (D ⟨((b x : F), (r : ℝ)), ⟨(b x).property, r.property⟩⟩ : F) =
          C ⟨((x : E), (r : ℝ)), ⟨x.property, r.property⟩⟩) ∧
      ∀ J : Set ℝ,
        (fun z : (B ×ˢ I : Set (F × ℝ)) => (D z : F)) ''
            {z | (z : F × ℝ).2 ∈ J} =
          (fun z : (A ×ˢ I : Set (E × ℝ)) => (C z : F)) ''
            {z | (z : E × ℝ).2 ∈ J} := by
  obtain ⟨f, hf, hfv⟩ := hC
  let a : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have ha : FinitePiecewiseAffineOn a A :=
    ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  have hbPL : b.IsFinitePL := by
    refine ⟨f ∘ a, hf.comp ha (fun x hx => ⟨hx, le_rfl, zero_le_one⟩), ?_⟩
    intro x
    exact (hb x).symm.trans (hfv ⟨((x : E), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  have hid : (Homeomorph.refl I).IsFinitePL :=
    ⟨id, ⟨KI, hKI, hKIs, KI.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ => rfl⟩
  let P := (Homeomorph.Set.prod B I).trans
    ((b.symm.prodCongr (Homeomorph.refl I)).trans (Homeomorph.Set.prod A I).symm)
  let D := P.trans C
  refine ⟨D, (hbPL.symm.prod hid).trans ⟨f, hf, hfv⟩, ?_, ?_, ?_⟩
  · intro x
    exact (hb (b.symm x)).trans (congrArg Subtype.val (b.apply_symm_apply x))
  · intro x r
    change (C ⟨((b.symm (b x) : E), (r : ℝ)), _⟩ : F) = _
    simp only [b.symm_apply_apply]
  · intro J
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨P z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨P.symm z, hz, ?_⟩
      change (C (P (P.symm z)) : F) = C z
      rw [P.apply_symm_apply]

omit [FiniteDimensional ℝ E] in


theorem IsFinitePL.exists_boundary_product_map
    {B T : Set E} {D : (B ×ˢ I : Set (E × ℝ)) ≃ₜ T} (hD : D.IsFinitePL)
    (hD0 : ∀ x : B,
      (D ⟨((x : E), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : E) = x) :
    ∃ (f : E × ℝ → E) (H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ f '' (B ×ˢ I)),
      H.IsFinitePL ∧ (∀ z, (H z : E) = f z) ∧
      f '' (B ×ˢ I) = T ∧
      (∀ x ∈ B, f (x, 0) = x) ∧
      (∀ z ∈ B ×ˢ I, f z ∈ B ↔ z.2 = 0) ∧
      (∀ z : (B ×ˢ I : Set (E × ℝ)), f z = D z) ∧
      ∀ J : Set ℝ,
        f '' (B ×ˢ (I ∩ J)) =
          (fun z : (B ×ˢ I : Set (E × ℝ)) => (D z : E)) ''
            {z | (z : E × ℝ).2 ∈ J} := by
  obtain ⟨f, hf, hfv⟩ := hD
  have himage : f '' (B ×ˢ I) = T := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hfv ⟨z, hz⟩ ▸ (D ⟨z, hz⟩).property
    · intro y hy
      obtain ⟨z, hz⟩ := D.surjective ⟨y, hy⟩
      exact ⟨z, z.property, (hfv z).symm.trans (congrArg Subtype.val hz)⟩
  let H := D.trans (Homeomorph.setCongr himage.symm)
  have hf0 (x : E) (hx : x ∈ B) : f (x, 0) = x :=
    (hfv ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩).symm.trans (hD0 ⟨x, hx⟩)
  refine ⟨f, H, (show D.IsFinitePL from ⟨f, hf, hfv⟩).setCongr rfl himage.symm,
    hfv, himage, hf0, ?_, (fun z => (hfv z).symm), ?_⟩
  · intro z hz
    constructor
    · intro hb
      have heq : D ⟨z, hz⟩ = D ⟨(f z, 0), ⟨hb, le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext ((hfv ⟨z, hz⟩).trans (hD0 ⟨f z, hb⟩).symm)
      exact congrArg (fun w : (B ×ˢ I : Set (E × ℝ)) => (w : E × ℝ).2)
        (D.injective heq)
    · intro ht
      have heq : f z = z.1 := by
        simpa only [← ht, Prod.eta] using hf0 z.1 hz.1
      exact heq ▸ hz.1
  · intro J
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, ⟨hz.1, hz.2.1⟩⟩, hz.2.2, hfv _⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, z.property.2, hz⟩, (hfv z).symm⟩

end Homeomorph
