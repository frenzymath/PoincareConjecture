import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteModelCollarTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SeparatedSphereCaps
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Geometry Geometry.SeparatedSphereCaps

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_lifted_original_boundary_collar
    {X E F ι κ : Type*} [TopologicalSpace X] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R B : Set X}
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N.space ×ˢ I))
    (hci : InjOn c (N.space ×ˢ I)) (hcR : MapsTo c (N.space ×ˢ I) R)
    (HB : N.space ≃ₜ B)
    (hc0 : ∀ x : N.space, c ((x : E), 0) = HB x)
    (f : X → F)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (H : R ≃ₜ K.space) (hH : ∀ x : R, (H x : F) = f x)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (N.space ×ˢ Ico 0 ε)))) :
    ∃ (g : (F × (κ → ℝ)) × ℝ → F × (κ → ℝ))
      (G : ((lift '' (f '' B)) ×ˢ I : Set ((F × (κ → ℝ)) × ℝ)) ≃ₜ
        g '' ((lift '' (f '' B)) ×ˢ I)),
      G.IsFinitePL ∧ (∀ z, (G z : F × (κ → ℝ)) = g z) ∧
      MapsTo g ((lift '' (f '' B)) ×ˢ I) (lift '' K.space) ∧
      (∀ x ∈ lift '' (f '' B), g (x, 0) = x) ∧
      (∀ z ∈ (lift '' (f '' B)) ×ˢ I, g z ∈ lift '' (f '' B) ↔ z.2 = 0) ∧
      (∀ (x : N.space) (r : I),
        g (lift (f (HB x)), (r : ℝ)) = lift (f (c ((x : E), (r : ℝ))))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen ((Subtype.val : (lift '' K.space : Set (F × (κ → ℝ))) → F × (κ → ℝ)) ⁻¹'
          (g '' ((lift '' (f '' B)) ×ˢ Ico 0 ε))) := by
  classical
  let L : F →ᴬ[ℝ] F × (κ → ℝ) :=
    (ContinuousAffineMap.id ℝ F).prod (ContinuousAffineMap.const ℝ F 0)
  have hL : FinitePiecewiseAffineOn L K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine L⟩
  obtain ⟨HL, hHL, hHLv⟩ := hL.exists_homeomorph_image
    (fun _ _ _ _ h => congrArg Prod.fst h)
  let Hlift : R ≃ₜ (lift '' K.space : Set (F × (κ → ℝ))) := H.trans HL
  let flift : X → F × (κ → ℝ) := fun x => lift (f x)
  have hFlift : ∀ i, LocallyPiecewiseAffineOn (flift ∘ (e i).symm) (e i).target := by
    intro i
    exact (hf i).prod_mk (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ V3 (0 : κ → ℝ)) (e i).open_target)
  have hFliftI : InjOn flift R := fun x hx y hy h => hfi hx hy (congrArg Prod.fst h)
  have hHlift (x : R) : (Hlift x : F × (κ → ℝ)) = flift x := by
    change (HL (H x) : F × (κ → ℝ)) = _
    rw [hHLv, hH]
    rfl
  obtain ⟨D, hD, hD0, hDx, hDopen⟩ := exists_finite_model_boundary_collar
    N hN c hc hci hcR flift hFlift hFliftI Hlift hHlift hδ hopen
  have hbase : (fun x => flift (c (x, 0))) '' N.space =
      (lift '' (f '' B) : Set (F × (κ → ℝ))) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change flift (c (x, 0)) ∈ lift '' (f '' B)
      rw [hc0 ⟨x, hx⟩]
      exact mem_image_of_mem lift (mem_image_of_mem f (HB ⟨x, hx⟩).property)
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      let y := HB.symm ⟨x, hx⟩
      refine ⟨y, y.property, ?_⟩
      change flift (c ((y : E), 0)) = flift x
      rw [hc0 y]
      exact congrArg flift (congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩))
  let D' := (Homeomorph.setCongr (congrArg (fun A : Set (F × (κ → ℝ)) => A ×ˢ I)
    hbase.symm)).trans D
  have hD' : D'.IsFinitePL := hD.setCongr (congrArg (fun A : Set (F × (κ → ℝ)) => A ×ˢ I)
    hbase) rfl
  have hD'0 (x : (lift '' (f '' B) : Set (F × (κ → ℝ)))) :
      (D' ⟨((x : F × (κ → ℝ)), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩ : F × (κ → ℝ)) = x :=
    hD0 ⟨x, hbase.symm.subset x.property⟩
  obtain ⟨g, G, hG, hGv, hgs, hg0, hgB, hgD, hgJ⟩ := hD'.exists_boundary_product_map hD'0
  refine ⟨g, G, hG, hGv, ?_, hg0, hgB, ?_, ?_⟩
  · intro z hz
    have hmem := hgs.subset (mem_image_of_mem g hz)
    obtain ⟨w, hw, hweq⟩ := hmem
    rw [← hweq]
    change flift (c w) ∈ lift '' K.space
    exact hHlift ⟨c w, hcR hw⟩ ▸ (Hlift ⟨c w, hcR hw⟩).property
  · intro x r
    have hp : lift (f (HB x)) ∈ (lift '' (f '' B) : Set (F × (κ → ℝ))) :=
      mem_image_of_mem lift (mem_image_of_mem f (HB x).property)
    rw [hgD ⟨(lift (f (HB x)), (r : ℝ)), ⟨hp, r.property⟩⟩]
    change (D ⟨(flift (HB x), (r : ℝ)), _⟩ : F × (κ → ℝ)) = _
    have hv := hDx x r
    simpa only [hc0 x] using hv
  · intro ε hε hεδ
    have ht : I ∩ Iio ε = Ico 0 ε := by
      ext r
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, h.2.le.trans (hεδ.trans hδ)⟩, h.2⟩⟩
    rw [← ht, hgJ]
    have heq : (fun z => (D' z : F × (κ → ℝ))) '' {z | (z : (F × (κ → ℝ)) × ℝ).2 ∈ Iio ε} =
        (fun z => (D z : F × (κ → ℝ))) '' {z | (z : (F × (κ → ℝ)) × ℝ).2 < ε} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, ⟨hbase.symm.subset z.property.1, z.property.2⟩⟩, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, ⟨hbase.subset z.property.1, z.property.2⟩⟩, hz, rfl⟩
    rw [heq]
    exact hDopen ε hε hεδ

end PoincareConjecture.M76
