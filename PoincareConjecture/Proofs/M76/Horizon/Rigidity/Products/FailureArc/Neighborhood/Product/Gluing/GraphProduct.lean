import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinitePLCover
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLCoreGraph
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel








set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

private theorem exists_homeomorph_compact_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {A : Set X} (hA : IsCompact A) (f : X → Y) (hf : Continuous f)
    (hi : InjOn f A) :
    ∃ H : A ≃ₜ f '' A, ∀ x : A, (H x : Y) = f x := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have he := (hf.comp continuous_subtype_val).isClosedEmbedding
    (fun x y hxy => Subtype.ext (hi x.property y.property hxy))
  have himage : range (fun x : A => f x) = f '' A := by
    change range (f ∘ (Subtype.val : A → X)) = _
    rw [range_comp, Subtype.range_coe]
  exact ⟨he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr himage), fun _ => rfl⟩

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finitePL_graph_product
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {E : κ → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (K : ∀ i, SimplicialComplex ℝ (E i)) (hK : ∀ i, (K i).faces.Finite)
    (p : ∀ i, E i × ℝ → X)
    (hp : ∀ i, PolyhedralPLInCharts e (p i) ((K i).space ×ˢ I))
    (hpi : ∀ i, InjOn (p i) ((K i).space ×ˢ I))
    (hcover : (⋃ i, p i '' ((K i).space ×ˢ {0})) = S)
    (H : S × I ≃ₜ R)
    (hvalue : ∀ i (x : (K i).space) (t : I),
      (H (⟨p i (x, 0), hcover ▸ mem_iUnion.mpr
        ⟨i, ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩⟩⟩, t) : X) = p i (x, t)) :
    ∃ (a : Finset R) (F : X → (a → ℝ × V3))
      (HG : ((F '' S) ×ˢ I) ≃ₜ (F '' R)),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ x ∈ R, ∀ y : X, F x = F y → x = y) ∧
      HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
      (∀ (x : S) (t : I),
        (HG ⟨(F x, t), ⟨mem_image_of_mem F x.property, t.property⟩⟩ : a → ℝ × V3) =
          F (H (x, t))) ∧
      ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (a → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ F) (e i) V := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨a, c, Q, F, _, hQe, hRQ, hFc, hFPL, hproj, hsep⟩ :=
    OpenPartialHomeomorph.exists_locallyPL_graph_separating_compact_core
      e he.compatible he.cover hR isOpen_univ (subset_univ _)
  have hseparate : ∀ x ∈ R, ∀ y : X, F x = F y → x = y := by
    intro x hx y hxy
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hRQ hx)
    exact hsep x (mem_iUnion.mpr ⟨i, interior_subset hxi⟩) y hxy
  have hbottom (i : κ) {x : E i} (hx : x ∈ (K i).space) : p i (x, 0) ∈ S :=
    hcover ▸ mem_iUnion.mpr ⟨i, ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩⟩
  have hpR (i : κ) : MapsTo (p i) ((K i).space ×ˢ I) R := by
    intro z hz
    rw [← hvalue i ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩]
    exact (H _).property
  have hSR : S ⊆ R := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
    exact hpR i ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ I from ⟨le_rfl, zero_le_one⟩)⟩
  have hS : IsCompact S := by
    rw [← hcover]
    apply isCompact_iUnion
    intro i
    apply (((K i).isCompact_space_of_finite (hK i)).prod isCompact_singleton).image_of_continuousOn
    exact (hp i).continuousOn.mono (prod_mono Subset.rfl (by
      intro t ht
      rw [mem_singleton_iff.mp ht]
      exact ⟨le_rfl, zero_le_one⟩))
  obtain ⟨HS, hHS⟩ := exists_homeomorph_compact_image hS F hFc
    (fun x hx y _ hxy => hseparate x (hSR hx) y hxy)
  obtain ⟨HR, hHR⟩ := exists_homeomorph_compact_image hR F hFc
    (fun x hx y _ hxy => hseparate x hx y hxy)
  let HG : ((F '' S) ×ˢ I) ≃ₜ (F '' R) :=
    (Homeomorph.Set.prod (F '' S) I).trans
      ((HS.symm.prodCongr (Homeomorph.refl I)).trans (H.trans HR))
  have hHG (x : S) (t : I) :
      (HG ⟨(F x, t), ⟨mem_image_of_mem F x.property, t.property⟩⟩ : a → ℝ × V3) =
        F (H (x, t)) := by
    have hx : (⟨F x, mem_image_of_mem F x.property⟩ : F '' S) = HS x :=
      Subtype.ext (hHS x).symm
    change (HR (H (HS.symm ⟨F x, _⟩, t)) : a → ℝ × V3) = _
    rw [hx, HS.symm_apply_apply, hHR]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J, hJ, hJI, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hFp (i : κ) : FinitePiecewiseAffineOn (F ∘ p i) ((K i).space ×ˢ I) := by
    obtain ⟨L, hL, hLs, _⟩ := (K i).exists_finite_triangulation_prod J (hK i) hJ
    rw [hJI] at hLs
    have h := ((hLs.symm ▸ hp i) : PolyhedralPLInCharts e (p i) L.space)
    simpa only [hLs] using h.finitePiecewiseAffineOn_comp L hL hFPL
  let bottom (i : κ) : E i → (a → ℝ × V3) := fun x => F (p i (x, 0))
  have hFbottom (i : κ) : FinitePiecewiseAffineOn (bottom i) (K i).space := by
    let z : E i →ᴬ[ℝ] (E i × ℝ) :=
      (ContinuousAffineMap.id ℝ (E i)).prod (ContinuousAffineMap.const ℝ (E i) 0)
    have hz : FinitePiecewiseAffineOn z (K i).space :=
      ⟨K i, hK i, rfl, (K i).affineOnFaces_affine z⟩
    exact (hFp i).comp hz (fun x hx => ⟨hx, le_rfl, zero_le_one⟩)
  let q (i : κ) : E i × ℝ → (a → ℝ × V3) × ℝ := Prod.map (bottom i) id
  have hq (i : κ) : FinitePiecewiseAffineOn (q i) ((K i).space ×ˢ I) :=
    (hFbottom i).prodMap hid
  have hqi (i : κ) : InjOn (q i) ((K i).space ×ˢ I) := by
    intro x hx y hy hxy
    have hFxy : F (p i (x.1, 0)) = F (p i (y.1, 0)) := congrArg Prod.fst hxy
    have hx0 : (x.1, (0 : ℝ)) ∈ (K i).space ×ˢ I := ⟨hx.1, le_rfl, zero_le_one⟩
    have hy0 : (y.1, (0 : ℝ)) ∈ (K i).space ×ˢ I := ⟨hy.1, le_rfl, zero_le_one⟩
    have hp0 := hpi i hx0 hy0 (hseparate _ (hpR i hx0) _ hFxy)
    apply Prod.ext
    · exact (Prod.mk.inj hp0).1
    · exact congrArg (fun z : (a → ℝ × V3) × ℝ => z.2) hxy
  have hqcover : (⋃ i, q i '' ((K i).space ×ˢ I)) = (F '' S) ×ˢ I := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
      exact ⟨mem_image_of_mem F (hbottom i hx.1), hx.2⟩
    · rintro ⟨⟨x, hx, hFx⟩, ht⟩
      obtain ⟨i, y, hy, hpy⟩ := mem_iUnion.mp (hcover.symm ▸ hx)
      refine mem_iUnion.mpr ⟨i, ⟨(y.1, z.2), ⟨hy.1, ht⟩, ?_⟩⟩
      apply Prod.ext
      · change F (p i (y.1, 0)) = z.1
        have hy0 : y.2 = 0 := hy.2
        rw [← hy0]
        exact (congrArg F hpy).trans hFx
      · rfl
  have hHGPL : HG.IsFinitePL := by
    apply Homeomorph.isFinitePL_of_parametrized_cover HG q
      (fun i => (K i).space ×ˢ I) hq hqi hqcover (fun i => F ∘ p i) hFp
    intro i x
    exact (hHG ⟨p i ((x : E i × ℝ).1, 0), hbottom i x.property.1⟩
      ⟨(x : E i × ℝ).2, x.property.2⟩).trans
      (congrArg F (hvalue i ⟨(x : E i × ℝ).1, x.property.1⟩
        ⟨(x : E i × ℝ).2, x.property.2⟩))
  refine ⟨a, F, HG, hFc, hFPL, hseparate, hHGPL, hHGPL.symm, hHG, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hRQ hx)
  let b : (a → ℝ × V3) →ᴬ[ℝ] V3 :=
    ((ContinuousLinearMap.snd ℝ ℝ V3).comp (ContinuousLinearMap.proj i)).toContinuousAffineMap
  exact ⟨c i, interior (Q i), b, isOpen_interior, hxi,
    fun y hy => (hQe i (interior_subset hy)).1,
    fun y hy => congrArg Prod.snd (hproj i (interior_subset hy))⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
