import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.BoundaryProductNormalization
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem isOpen_relative_model_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R S : Set X} {P : Set Y} (H : R ≃ₜ P) (f : X → Y)
    (hH : ∀ x : R, (H x : Y) = f x) (hSR : S ⊆ R)
    (hS : IsOpen ((Subtype.val : R → X) ⁻¹' S)) :
    IsOpen ((Subtype.val : P → Y) ⁻¹' (f '' S)) := by
  have heq : (Subtype.val : P → Y) ⁻¹' (f '' S) =
      H '' ((Subtype.val : R → X) ⁻¹' S) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hSR hx⟩, hx, Subtype.ext ((hH _).trans hxy)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hH x).symm⟩
  rw [heq]
  exact H.isOpenMap _ hS

theorem exists_finite_model_boundary_product
    {X E F ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (K.space ×ˢ I))
    (hci : InjOn c (K.space ×ˢ I)) (hcR : MapsTo c (K.space ×ˢ I) R)
    (f : X → F)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) :
    ∃ D : (((fun x => f (c (x, 0))) '' K.space) ×ˢ I : Set (F × ℝ)) ≃ₜ
        (f ∘ c) '' (K.space ×ˢ I),
      D.IsFinitePL ∧
      (∀ x : (fun x => f (c (x, 0))) '' K.space,
        (D ⟨((x : F), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F) = x) ∧
      (∀ (x : K.space) (r : I),
        (D ⟨(f (c ((x : E), 0)), (r : ℝ)),
          ⟨mem_image_of_mem _ x.property, r.property⟩⟩ : F) =
          f (c ((x : E), (r : ℝ)))) ∧
      ∀ J : Set ℝ,
        (fun z => (D z : F)) '' {z | (z : F × ℝ).2 ∈ J} =
          f '' (c '' (K.space ×ˢ (I ∩ J))) := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨KP, hKP, hKPs, _⟩ := K.exists_finite_triangulation_prod KI hK hKI
  rw [hKIs] at hKPs
  have hfc : FinitePiecewiseAffineOn (f ∘ c) (K.space ×ˢ I) := by
    have h : PolyhedralPLInCharts e c KP.space := hKPs.symm ▸ hc
    exact hKPs ▸ h.finitePiecewiseAffineOn_comp KP hKP hf
  have hfci : InjOn (f ∘ c) (K.space ×ˢ I) := by
    intro x hx y hy hxy
    exact hci hx hy (hfi (hcR hx) (hcR hy) hxy)
  obtain ⟨C, hC, hCv⟩ := hfc.exists_homeomorph_image hfci
  let a : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have ha : FinitePiecewiseAffineOn a K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine a⟩
  have hb : FinitePiecewiseAffineOn (fun x => f (c (x, 0))) K.space :=
    hfc.comp ha (fun x hx => ⟨hx, le_rfl, zero_le_one⟩)
  have hbi : InjOn (fun x => f (c (x, 0))) K.space := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hfci ⟨hx, le_rfl, zero_le_one⟩
      ⟨hy, le_rfl, zero_le_one⟩ hxy)
  obtain ⟨b, _, hbv⟩ := hb.exists_homeomorph_image hbi
  have hCb (x : K.space) :
      (C ⟨((x : E), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F) = b x :=
    (hCv _).trans (hbv x).symm
  obtain ⟨D, hD, hD0, hDb, hDJ⟩ := hC.exists_boundary_normalized_product K hK rfl b hCb
  refine ⟨D, hD, hD0, ?_, ?_⟩
  · intro x r
    have h := (hDb x r).trans (hCv _)
    simpa only [hbv x, Function.comp_apply] using h
  · intro J
    rw [hDJ]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨c z, ⟨z, ⟨z.property.1, z.property.2, hz⟩, rfl⟩, (hCv z).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, ⟨hz.1, hz.2.1⟩⟩, hz.2.2, hCv _⟩

theorem exists_finite_model_boundary_collar
    {X E F ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {P : Set F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (K.space ×ˢ I))
    (hci : InjOn c (K.space ×ˢ I)) (hcR : MapsTo c (K.space ×ˢ I) R)
    (f : X → F)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) (H : R ≃ₜ P) (hH : ∀ x : R, (H x : F) = f x)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico 0 ε)))) :
    ∃ D : (((fun x => f (c (x, 0))) '' K.space) ×ˢ I : Set (F × ℝ)) ≃ₜ
        (f ∘ c) '' (K.space ×ˢ I),
      D.IsFinitePL ∧
      (∀ x : (fun x => f (c (x, 0))) '' K.space,
        (D ⟨((x : F), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F) = x) ∧
      (∀ (x : K.space) (r : I),
        (D ⟨(f (c ((x : E), 0)), (r : ℝ)),
          ⟨mem_image_of_mem _ x.property, r.property⟩⟩ : F) =
          f (c ((x : E), (r : ℝ)))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen ((Subtype.val : P → F) ⁻¹'
          ((fun z => (D z : F)) '' {z | (z : F × ℝ).2 < ε})) := by
  obtain ⟨D, hD, hD0, hDx, hDJ⟩ :=
    exists_finite_model_boundary_product K hK c hc hci hcR f hf hfi
  refine ⟨D, hD, hD0, hDx, ?_⟩
  intro ε hε hεδ
  have hstrip := hDJ {r : ℝ | r < ε}
  simp only [mem_ofPred_eq] at hstrip
  rw [hstrip]
  have htime : I ∩ {r : ℝ | r < ε} = Ico 0 ε := by
    ext r
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.le.trans (hεδ.trans hδ)⟩, h.2⟩
  rw [htime]
  apply isOpen_relative_model_image H f hH _ (hopen ε hε hεδ)
  rintro _ ⟨z, hz, rfl⟩
  exact hcR ⟨hz.1, hz.2.1, hz.2.2.le.trans (hεδ.trans hδ)⟩

end PoincareConjecture.M76
