import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.CompressionPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalRegionCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.LocalEmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

local notation "V3" => (Fin 3 → ℝ)

private theorem chartwisePLOn_fixed_off_boundary_neighborhood
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (he : PLDomain e R) (hD : IsClosed D) (hfront : frontier R ⊆ D)
    (G : C(R, R)) (hfix : ∀ x : R, (x : X) ∉ D → G x = x) :
    ChartwisePLOn e e G ((Subtype.val : R → X) ⁻¹' Dᶜ) := by
  exact chartwisePLOn_collar_exterior_identity he hD hfront G hfix

theorem chartwisePL_original_collar_region_motion
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
    (m : (K.space ×ˢ Icc (0 : ℝ) eps) ≃ₜ (K.space ×ˢ Icc (0 : ℝ) eps))
    (hm : m.IsFinitePL)
    (hsmall : ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
      (G ⟨c z, hmap ⟨z.property.1, z.property.2.1, z.property.2.2.trans hed.le⟩⟩ : X) = c (m z))
    (hout : ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G x = x) :
    ChartwisePLMap e e G := by
  classical
  let P := K.space ×ˢ Icc (0 : ℝ) eps
  let B := K.space ×ˢ Icc (0 : ℝ) delta
  let D := c '' P
  have hPB : P ⊆ B := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hed.le⟩
  have hD : IsClosed D := (((K.isCompact_space_of_finite hK).prod isCompact_Icc).image_of_continuousOn
    (hcPL.continuousOn.mono hPB)).isClosed
  obtain ⟨f, hf, hfmap, hfv⟩ := exists_original_collar_extension_coordinates
    K hK heps hed.le c hemb hmap G m hm hsmall hout
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK (heps.trans hed)
  have hcomp := hcPL.comp_finitePiecewiseAffineOn J hJ (hJs.symm ▸ hf) (hJs.symm ▸ hfmap)
  have hU := chartwisePLOn_fixed_off_boundary_neighborhood he hD hfront G hout
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

end PoincareConjecture.M76.CollarIsotopy
