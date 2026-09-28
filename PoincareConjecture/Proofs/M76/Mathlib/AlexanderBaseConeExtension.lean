import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




noncomputable def radialExtension (L : E →ₗ[ℝ] ℝ) (f : E → F) (x : E) : F :=
  L x • f ((L x)⁻¹ • x)




theorem radialExtension_smul (L : E →ₗ[ℝ] ℝ) (f : E → F)
    {y : E} (hy : L y = 1) (r : ℝ) :
    L.radialExtension f (r • y) = r • f y := by
  by_cases hr : r = 0
  · simp [radialExtension, hr]
  · simp [radialExtension, map_smul, hy, smul_eq_mul, inv_smul_smul₀ hr]




theorem radialExtension_image_convexJoin (L : E →ₗ[ℝ] ℝ) (f : E → F)
    {s : Set E} (hL : ∀ x ∈ s, L x = 1) :
    L.radialExtension f '' convexJoin ℝ {0} s = convexJoin ℝ {0} (f '' s) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, r, hr, rfl⟩ := (mem_convexJoin_zero_iff s x).mp hx
    rw [L.radialExtension_smul f (hL y hy)]
    exact (mem_convexJoin_zero_iff _ _).mpr ⟨f y, mem_image_of_mem f hy, r, hr, rfl⟩
  · intro hz
    obtain ⟨w, ⟨y, hy, rfl⟩, r, hr, rfl⟩ :=
      (mem_convexJoin_zero_iff (f '' s) z).mp hz
    exact ⟨r • y, (mem_convexJoin_zero_iff s _).mpr ⟨y, hy, r, hr, rfl⟩,
      L.radialExtension_smul f (hL y hy) r⟩





theorem injOn_radialExtension (L : E →ₗ[ℝ] ℝ) (M : F →ₗ[ℝ] ℝ)
    {f : E → F} {s : Set E} (hL : ∀ x ∈ s, L x = 1)
    (hM : ∀ x ∈ s, M (f x) = 1) (hf : InjOn f s) :
    InjOn (L.radialExtension f) (convexJoin ℝ {0} s) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, r, _, rfl⟩ := (mem_convexJoin_zero_iff s x).mp hx
  obtain ⟨v, hv, t, _, rfl⟩ := (mem_convexJoin_zero_iff s y).mp hy
  rw [L.radialExtension_smul f (hL u hu), L.radialExtension_smul f (hL v hv)] at hxy
  have hrt : r = t := by
    have h := congrArg M hxy
    simpa only [map_smul, hM u hu, hM v hv, smul_eq_mul, mul_one] using h
  subst t
  by_cases hr : r = 0
  · simp [hr]
  · rw [hf hu hv (smul_right_injective F hr hxy)]

end LinearMap

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [DecidableEq E] {K : SimplicialComplex ℝ E} {f : E → F}





theorem AffineOnFaces.radialExtension (hf : K.AffineOnFaces f)
    (L : E →ₗ[ℝ] ℝ) (hL : ∀ x ∈ K.space, L x = 1) :
    (K.coneAtZero (K.linearIndependent_faces_of_linear_level L one_ne_zero hL)
      (L.injOn_normalize_of_level one_ne_zero hL)).AffineOnFaces
      (L.radialExtension f) := by
  intro s hs
  rcases hs.2 with he | hbase
  · have hs0 : s = {0} :=
      ((Finset.erase_eq_empty_iff s 0).mp he).resolve_left hs.1.ne_empty
    refine ⟨ContinuousAffineMap.const ℝ E (0 : F), ?_⟩
    intro x hx
    have hx0 : x = 0 := by simpa [hs0] using hx
    simp [hx0, LinearMap.radialExtension]
  · obtain ⟨a, ha⟩ := hf _ hbase
    let b : E →ᴬ[ℝ] F :=
      (a.contLinear + L.toContinuousLinearMap.smulRight (a 0)).toContinuousAffineMap
    refine ⟨b, ?_⟩
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0, LinearMap.radialExtension, b]
    · have hsub : (s : Set E) ⊆ insert (0 : E) (s.erase 0 : Set E) := by
        intro y hy
        by_cases hy0 : y = 0
        · exact Or.inl hy0
        · exact Or.inr (Finset.mem_erase.mpr ⟨hy0, hy⟩)
      obtain ⟨y, hy, r, _, rfl⟩ :=
        exists_pos_smul_of_mem_convexHull_insert_zero (convexHull_mono hsub hx) hx0
      have hLy : L y = 1 := hL y (K.convexHull_subset_space hbase hy)
      have haform : a y = a.contLinear y + a 0 :=
        congrFun (a : E →ᵃ[ℝ] F).decomp y
      rw [L.radialExtension_smul f hLy, ha hy, haform]
      simp [b, map_smul, hLy, smul_add]

end Geometry.SimplicialComplex

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem FinitePiecewiseAffineOn.radialExtension {f : E → F} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) (hne : s.Nonempty)
    (L : E →ₗ[ℝ] ℝ) (hL : ∀ x ∈ s, L x = 1) :
    FinitePiecewiseAffineOn (L.radialExtension f) (convexJoin ℝ {0} s) := by
  classical
  obtain ⟨K, hK, rfl, hf⟩ := hf
  let hlin := K.linearIndependent_faces_of_linear_level L one_ne_zero hL
  let hrad := L.injOn_normalize_of_level one_ne_zero hL
  refine ⟨K.coneAtZero hlin hrad, SimplicialComplex.finite_coneAtZero_faces hK hlin hrad,
    K.coneAtZero_space_eq_convexJoin hlin hrad hne, ?_⟩
  exact hf.radialExtension L hL

end Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem IsFinitePL.exists_radial_cone_extension {s : Set E} {t : Set F}
    {e : s ≃ₜ t} (he : e.IsFinitePL) (hne : s.Nonempty)
    (L : E →ₗ[ℝ] ℝ) (M : F →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ s, L x = 1) (hM : ∀ y ∈ t, M y = 1) :
    ∃ H : convexJoin ℝ {0} s ≃ₜ convexJoin ℝ {0} t, H.IsFinitePL ∧
      ∀ (y : s) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1),
        (H ⟨r • (y : E), (mem_convexJoin_zero_iff s _).mpr
          ⟨y, y.property, r, hr, rfl⟩⟩ : F) = r • (e y : F) := by
  obtain ⟨f, hf, hef⟩ := he
  have hfm : MapsTo f s t := fun x hx => by
    rw [← hef ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hfi : InjOn f s := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  have hft : f '' s = t := by
    apply Subset.antisymm (image_subset_iff.mpr hfm)
    intro y hy
    exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property,
      (hef _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
  have hF := hf.radialExtension hne L hL
  have hFi := L.injOn_radialExtension M hL (fun x hx => hM _ (hfm hx)) hfi
  have him : L.radialExtension f '' convexJoin ℝ {0} s = convexJoin ℝ {0} t := by
    rw [L.radialExtension_image_convexJoin f hL, hft]
  obtain ⟨G, ⟨g, hg, hGg⟩, hG⟩ := hF.exists_homeomorph_image hFi
  let H := G.trans (Homeomorph.setCongr him)
  refine ⟨H, ⟨g, hg, hGg⟩, ?_⟩
  intro y r hr
  change (G _ : F) = _
  rw [hG, L.radialExtension_smul f (hL y y.property), ← hef]

end Homeomorph
