import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteLabelHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import Mathlib.RingTheory.Finiteness.Prod

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_finite_collar_phase_products
    {E V X Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    {e : ι → OpenPartialHomeomorph X V}
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    {S : Set X} (HB : L.space ≃ₜ S) (q : C(X, Y))
    {D : Set Y} (hD : D.Finite) (hS : S = q ⁻¹' D)
    {c : E × ℝ → X}
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = (HB x : X))
    {delta : ℝ} (hdeltaOne : delta ≤ 1)
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ delta →
      IsOpen (c '' (L.space ×ˢ Ioo (-eps) eps)))
    {v : Y} (hv : v ∈ D) :
    ∃ (J : SimplicialComplex ℝ E) (H : J.space ≃ₜ (q ⁻¹' {v} : Set X)),
      J.faces.Finite ∧ J ≤ L ∧
      J.space = L.space ∩ (fun x => q (c (x, 0))) ⁻¹' {v} ∧
      (∀ x : J.space, (H x : X) = c ((x : E), 0)) ∧
      PolyhedralPLInCharts e (fun x => c (x, 0)) J.space ∧
      (∀ rho : ℝ, 0 < rho → rho ≤ delta →
        ∃ K : SimplicialComplex ℝ (E × ℝ),
          K.faces.Finite ∧ K.space = J.space ×ˢ Icc (-rho) rho ∧
          PolyhedralPLInCharts e c K.space ∧
          Topology.IsEmbedding (fun z : K.space => c z)) ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ delta →
        IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps)) := by
  obtain ⟨J, H, hJ, hJL, hJs, hH, hclopen⟩ :=
    L.exists_finite_label_homeomorph hL HB q hD hS (fun x => c (x, 0)) hbase hv
  have hsub : J.space ⊆ L.space := SimplicialComplex.space_subset_of_le hJL
  have hzeroPL : PolyhedralPLInCharts e (fun x => c (x, 0)) J.space := by
    let a : E →ᴬ[ℝ] (E × ℝ) :=
      (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
    have ha : FinitePiecewiseAffineOn (fun x : E => (x, (0 : ℝ))) J.space :=
      (J.affineOnFaces_affine a).finitePiecewiseAffineOn hJ
    have hmap : MapsTo (fun x : E => (x, (0 : ℝ)))
        J.space (L.space ×ˢ Icc (-1 : ℝ) 1) := by
      intro x hx
      exact ⟨hsub hx, by norm_num⟩
    exact hc.comp_finitePiecewiseAffineOn J hJ ha hmap
  refine ⟨J, H, hJ, hJL, hJs, hH, hzeroPL, ?_, ?_⟩
  · intro rho hrho hrhoDelta
    obtain ⟨K, hK, hKs⟩ := J.exists_finite_interval_product hJ
      (show -rho < rho by linarith)
    have hKL : K.space ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
      intro z hz
      have hz' := hKs.subset hz
      exact ⟨hsub hz'.1, by linarith [hz'.2.1], by linarith [hz'.2.2]⟩
    exact ⟨K, hK, hKs, hc.restrict_finite K hK hKL,
      hi.comp (Topology.IsEmbedding.inclusion hKL)⟩
  · intro eps heps hepsDelta
    let P : Set (E × ℝ) := L.space ×ˢ Icc (-1 : ℝ) 1
    let base : P → L.space := fun z => ⟨z.val.1, z.property.1⟩
    let time : P → ℝ := fun z => z.val.2
    have hbaseCont : Continuous base :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have htimeCont : Continuous time := continuous_snd.comp continuous_subtype_val
    let A : Set P :=
      base ⁻¹' {x : L.space | q (c ((x : E), 0)) = v} ∩ time ⁻¹' Ioo (-eps) eps
    have hA : IsOpen A :=
      (hclopen.2.preimage hbaseCont).inter (isOpen_Ioo.preimage htimeCont)
    let f : P → X := fun z => c z
    have hf : Topology.IsEmbedding f := hi
    let W : Set X := c '' (L.space ×ˢ Ioo (-eps) eps)
    have hW : IsOpen W := hopen eps heps hepsDelta
    have hAW : f '' A ⊆ W := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, hz.2⟩, rfl⟩
    have hWf : W ⊆ range f := by
      rintro y ⟨z, hz, rfl⟩
      have hzP : z ∈ P :=
        ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact ⟨⟨z, hzP⟩, rfl⟩
    have himage : f '' A = c '' (J.space ×ˢ Ioo (-eps) eps) := by
      apply Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        have hzJ : z.val.1 ∈ J.space :=
          hJs.symm.subset ⟨z.property.1, hz.1⟩
        exact ⟨z, ⟨hzJ, hz.2⟩, rfl⟩
      · rintro y ⟨z, hz, rfl⟩
        have hzP : z ∈ P :=
          ⟨hsub hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
        refine ⟨⟨z, hzP⟩, ?_, rfl⟩
        exact ⟨(hJs.subset hz.1).2, hz.2⟩
    rw [← himage]
    exact hf.isInducing.isOpen_image_of_subset_open hA hW hAW hWf

end Geometry.SimplicialComplex
