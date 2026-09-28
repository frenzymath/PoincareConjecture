import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasTransitionSigns
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageReparameterization
import PoincareConjecture.Proofs.M76.Mathlib.AffineChartInclusion
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
open Set

namespace Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLAffineWitness.affine_conjugate
    {h : OpenPartialHomeomorph E E} {g : OpenPartialHomeomorph F F}
    {x : E} {A : E →ᴬ[ℝ] E} (hA : IsPLAffineWitness h x A)
    (L : E ≃ᴬ[ℝ] F) (hsource : MapsTo L h.source g.source)
    (heq : ∀ y ∈ h.source, g (L y) = L (h y)) :
    IsPLAffineWitness g (L x)
      (L.toContinuousAffineMap.comp (A.comp L.symm.toContinuousAffineMap)) := by
  classical
  obtain ⟨K, hK, hxK, hKs, hf, t, ht, htc, hxt, htA⟩ := hA
  let hL : K.AffineOnFaces (L : E → F) := K.affineOnFaces_affine L.toContinuousAffineMap
  let J := hL.embeddedImage L.injective.injOn
  have hJs : J.space = L '' K.space := hL.embeddedImage_space _
  have hxJ : L x ∈ interior J.space := by
    rw [hJs, show L '' K.space = L.toHomeomorph '' K.space from rfl,
      ← L.toHomeomorph.image_interior]
    exact mem_image_of_mem _ hxK
  have hJsource : J.space ⊆ g.source := by
    rw [hJs]
    rintro _ ⟨y, hy, rfl⟩
    exact hsource (hKs hy)
  have hgf : J.AffineOnFaces g := by
    have hc := (hL.comp_inverse_on_embeddedImage hf L.injective.injOn
      (fun _ _ => L.symm_apply_apply _)).postcomp L.toContinuousAffineMap
    apply hc.congr
    rw [hJs]
    rintro _ ⟨y, hy, rfl⟩
    change L (h (L.symm (L y))) = g (L y)
    rw [L.symm_apply_apply]
    exact (heq y (hKs hy)).symm
  have hhull : convexHull ℝ ((t.image L : Finset F) : Set F) =
      L '' convexHull ℝ (t : Set E) := by
    rw [Finset.coe_image]
    exact (L.toAffineEquiv.toAffineMap.image_convexHull _).symm
  refine ⟨J, hL.embeddedImage_finite _ hK, hxJ, hJsource, hgf, t.image L, ?_, ?_, ?_, ?_⟩
  · change t.image L ∈ (hL.embeddedImage L.injective.injOn).faces
    rw [hL.embeddedImage_faces]
    exact ⟨t, ht, rfl⟩
  · rw [Finset.card_image_iff.mpr L.injective.injOn, htc,
      L.toAffineEquiv.linear.finrank_eq]
  · rw [hhull]
    exact mem_image_of_mem _ hxt
  · rw [hhull]
    rintro _ ⟨y, hy, rfl⟩
    change g (L y) = L (A (L.symm (L y)))
    rw [L.symm_apply_apply, heq y (hKs (K.convexHull_subset_space ht hy)), htA hy]

theorem plLocalSign_affine_conjugate
    (h : OpenPartialHomeomorph E E) (g : OpenPartialHomeomorph F F)
    (hh : h ∈ piecewiseAffineGroupoid E) (hg : g ∈ piecewiseAffineGroupoid F)
    (L : E ≃ᴬ[ℝ] F) (hsource : MapsTo L h.source g.source)
    (heq : ∀ y ∈ h.source, g (L y) = L (h y)) (x : h.source) :
    plLocalSign g hg ⟨L x, hsource x.property⟩ = plLocalSign h hh x := by
  obtain ⟨A, hA⟩ := exists_plAffineWitness h hh x.property
  rw [plLocalSign_eq_of_witness g hg _ (hA.affine_conjugate L hsource heq),
    plLocalSign_eq_of_witness h hh x hA]
  congr 1
  exact LinearMap.det_conj A.toAffineMap.linear L.toAffineEquiv.linear

variable {X ι : Type*} [TopologicalSpace X]

theorem affine_model_plAtlas_compatible
    (q : ι → OpenPartialHomeomorph X E)
    (hq : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid E)
    (L : E ≃ᴬ[ℝ] F) :
    ∀ i j, ((q i).transHomeomorph L.toHomeomorph).symm.trans
      ((q j).transHomeomorph L.toHomeomorph) ∈ piecewiseAffineGroupoid F := by
  intro i j
  apply OpenPartialHomeomorph.affine_inclusion_transition_mem_piecewiseAffineGroupoid
    id Function.injective_id (q i) (q j) (hq i j) L L
  · intro y hy
    exact ⟨hy, rfl⟩
  · intro x hx
    exact ⟨x, hx, rfl, rfl⟩

theorem plAtlasTransitionSign_affine_model
    (q : ι → OpenPartialHomeomorph X E)
    (hq : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid E)
    (L : E ≃ᴬ[ℝ] F) (i j : ι)
    (x : ((q i).source ∩ (q j).source : Set X)) :
    plAtlasTransitionSign (fun k => (q k).transHomeomorph L.toHomeomorph)
      (affine_model_plAtlas_compatible q hq L) i j x =
        plAtlasTransitionSign q hq i j x := by
  let h := (q i).symm.trans (q j)
  let g := ((q i).transHomeomorph L.toHomeomorph).symm.trans
    ((q j).transHomeomorph L.toHomeomorph)
  have hsource : MapsTo L h.source g.source := by
    intro y hy
    change L.symm (L y) ∈ (q i).target ∧
      (q i).symm (L.symm (L y)) ∈ (q j).source
    rw [L.symm_apply_apply]
    exact hy
  have heq (y : E) (_hy : y ∈ h.source) : g (L y) = L (h y) := by
    change L (q j ((q i).symm (L.symm (L y)))) = L (q j ((q i).symm y))
    rw [L.symm_apply_apply]
  have hx : q i x ∈ h.source := by
    refine ⟨(q i).map_source x.property.1, ?_⟩
    change (q i).symm (q i x) ∈ (q j).source
    rw [(q i).left_inv x.property.1]
    exact x.property.2
  exact plLocalSign_affine_conjugate h g (hq i j)
    (affine_model_plAtlas_compatible q hq L i j) L hsource heq ⟨q i x, hx⟩

end Geometry
