import PoincareConjecture.Proofs.M76.Rigidity.LocalEmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition








set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem chartwisePLOn_collar_exterior_identity
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (he : PLDomain e R) (hD : IsClosed D) (hfront : frontier R ⊆ D)
    (G : C(R, R)) (hfix : ∀ x : R, (x : X) ∉ D → G x = x) :
    ChartwisePLOn e e G ((Subtype.val : R → X) ⁻¹' Dᶜ) := by
  refine ⟨he, he, hD.isOpen_compl.preimage continuous_subtype_val, ?_⟩
  intro x hx
  have hxin : (x : X) ∈ interior R :=
    (mem_interior_iff_notMem_frontier x.property).mpr (fun h => hx (hfront h))
  obtain ⟨i, hxi⟩ := he.cover x
  let O : Set V3 := (e i).target ∩ (e i).symm ⁻¹' (interior R ∩ Dᶜ)
  have hO : IsOpen O := (e i).symm.continuousOn.isOpen_inter_preimage
    (e i).open_target (isOpen_interior.inter hD.isOpen_compl)
  have hxe : e i x ∈ O := ⟨(e i).map_source hxi, by
    change (e i).symm (e i x) ∈ interior R ∩ Dᶜ
    rw [(e i).left_inv hxi]
    exact ⟨hxin, hx⟩⟩
  obtain ⟨K, hK, hxK, hKO⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    (isCompact_singleton : IsCompact {e i x}) hO (singleton_subset_iff.mpr hxe)
  let W : Set R := (Subtype.val : R → X) ⁻¹'
    ((e i).source ∩ (e i) ⁻¹' interior K.space)
  have hW : IsOpen W := ((e i).isOpen_inter_preimage isOpen_interior).preimage continuous_subtype_val
  have hWU : W ⊆ (Subtype.val : R → X) ⁻¹' Dᶜ := by
    intro y hy
    have hn := (hKO (interior_subset hy.2)).2.2
    rwa [(e i).left_inv hy.1] at hn
  refine ⟨i, i, K, W, id, hK, hW, ⟨hxi, hxK (mem_singleton _)⟩,
    hWU, fun y hy => hy.1, ?_, fun z hz => (hKO hz).1, ?_,
    (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact interior_subset hy.2
  · intro z hz
    exact ⟨⟨(e i).symm z, interior_subset (hKO hz).2.1⟩, (hKO hz).2.2, rfl⟩
  · intro y hy hz
    have hn := (hKO hz).2.2
    rw [(e i).left_inv hy] at hn
    rw [hfix y hn]
    exact ⟨hy, rfl⟩

theorem chartwisePL_common_collar_compression
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X} (he : PLDomain e R)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {eps delta : ℝ} (heps : 0 < eps) (hed : eps < delta)
    (c : E × ℝ → X)
    (hcPL : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) delta))
    (hemb : IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) delta) => c z))
    (hmap : MapsTo c (K.space ×ˢ Icc (0 : ℝ) delta) R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) delta))))
    (hfront : frontier R ⊆ c '' (K.space ×ˢ Icc (0 : ℝ) eps))
    (G : C(R, R))
    (hsmall : ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
      (G ⟨c z, hmap ⟨z.property.1, z.property.2.1, z.property.2.2.trans hed.le⟩⟩ : X) =
        c (z.val.1, eps / 2 + z.val.2 / 2))
    (hout : ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G x = x) :
    ChartwisePLMap e e G := by
  classical
  let P := K.space ×ˢ Icc (0 : ℝ) eps
  let B := K.space ×ˢ Icc (0 : ℝ) delta
  let D := c '' P
  have hPB : P ⊆ B := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hed.le⟩
  have hD : IsClosed D := (((K.isCompact_space_of_finite hK).prod isCompact_Icc).image_of_continuousOn
    (hcPL.continuousOn.mono hPB)).isClosed
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK (heps.trans hed)
  let f : E × ℝ → E × ℝ := fun z => (z.1, max z.2 (eps / 2 + z.2 / 2))
  let first := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  let last := (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  let shifted : E × ℝ →ᴬ[ℝ] ℝ := (1 / 2 : ℝ) • last + ContinuousAffineMap.const ℝ (E × ℝ) (eps / 2)
  have hf : FinitePiecewiseAffineOn f J.space := by
    have ha := (J.affineOnFaces_affine first).finitePiecewiseAffineOn hJ
    have hb := (J.affineOnFaces_affine last).finitePiecewiseAffineOn hJ
    have hs := (J.affineOnFaces_affine shifted).finitePiecewiseAffineOn hJ
    apply (ha.prod_mk (hb.max hs)).congr
    intro z _
    change (z.1, max z.2 (1 / 2 * z.2 + eps / 2)) = _
    simp only [f, div_eq_mul_inv]
    congr 2
    ring
  have hfmap : MapsTo f B B := by
    intro z hz
    refine ⟨hz.1, le_max_of_le_left hz.2.1, max_le hz.2.2 ?_⟩
    linarith [hz.2.2]
  have hfv (z : B) : c (f z) = (G ⟨c z, hmap z.property⟩ : X) := by
    by_cases hz : z.val.2 ≤ eps
    · have hp : (z : E × ℝ) ∈ P := ⟨z.property.1, z.property.2.1, hz⟩
      rw [hsmall ⟨z, hp⟩]
      change c (z.val.1, max z.val.2 (eps / 2 + z.val.2 / 2)) = _
      rw [max_eq_right (by linarith)]
    · have hnot : c z ∉ D := by
        rintro ⟨w, hw, heq⟩
        have hsame := hemb.injective (a₁ := ⟨w, hPB hw⟩) (a₂ := z) heq
        have hheight := congrArg (fun t : B => t.val.2) hsame
        exact hz (hheight ▸ hw.2.2)
      rw [hout _ hnot]
      change c (z.val.1, max z.val.2 (eps / 2 + z.val.2 / 2)) = c z
      rw [max_eq_left (by linarith [lt_of_not_ge hz])]
  have hcomp := hcPL.comp_finitePiecewiseAffineOn J hJ hf (fun z hz => hfmap (hJs.subset hz))
  have hU := chartwisePLOn_collar_exterior_identity he hD hfront G hout
  apply chartwisePLMap_of_open_and_embedded_parameters (E := E × ℝ) e e G hU
  intro x hx
  have hxD : (x : X) ∈ D := not_not.mp hx
  let q (z : E × ℝ) : R := if hz : z ∈ B then ⟨c z, hmap hz⟩ else x
  have hqval (z : E × ℝ) (hz : z ∈ B) : (q z : X) = c z := by
    simp only [q, dif_pos hz]
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) J.space :=
    (hJs.symm ▸ hcPL).congr (fun z hz => (hqval z (hJs.subset hz)).symm)
  have hq : ContinuousOn q J.space := IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hi : IsEmbedding (fun z : J.space => q z) := by
    have hi0 := hemb.comp (Homeomorph.setCongr hJs).isEmbedding
    have hEq : (fun z : J.space => q z) =
        (fun z : J.space => (⟨c z, hmap (hJs.subset z.property)⟩ : R)) := by
      funext z
      exact Subtype.ext (hqval z (hJs.subset z.property))
    rw [hEq]
    exact hi0.codRestrict R (fun z => hmap (hJs.subset z.property))
  let W : Set R := (Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) delta))
  have hWrange : W ⊆ range (fun z : J.space => q z) := by
    rintro y ⟨z, hz, hzy⟩
    have hzB : z ∈ B := ⟨hz.1, hz.2.1, hz.2.2.le⟩
    exact ⟨⟨z, hJs.symm.subset hzB⟩, Subtype.ext ((hqval z hzB).trans hzy)⟩
  have hxW : x ∈ W := by
    obtain ⟨z, hz, hzx⟩ := hxD
    exact ⟨z, ⟨hz.1, hz.2.1, hz.2.2.trans_lt hed⟩, hzx⟩
  obtain ⟨z, hzx⟩ := hWrange hxW
  have hnhds : range (fun z : J.space => q z) ∈ 𝓝 x :=
    Filter.mem_of_superset (hopen.mem_nhds hxW) hWrange
  have hgq : PolyhedralPLInCharts e (fun z => (G (q z) : X)) J.space :=
    hcomp.congr (by
      intro z hz
      have hzB := hJs.subset hz
      change c (f z) = _
      rw [hfv ⟨z, hzB⟩]
      exact congrArg (fun y : R => (G y : X)) (Subtype.ext (hqval z hzB).symm))
  exact ⟨J, q, z, hJ, hq, hi, hzx, hnhds, hqPL, hgq⟩

end PoincareConjecture.M76
