import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.Compression
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.CompressionPL








set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_common_collar_region_compression
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
    (hopenSmall : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) eps))))
    (hopenLarge : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) delta))))
    (hfront : frontier R ⊆ c '' (K.space ×ˢ Icc (0 : ℝ) eps))
    (x₀ : R) :
    ∃ G : C(R, R), Function.Injective G ∧ ChartwisePLMap e e G ∧
      range (fun x => (G x : X)) = R \ (c '' (K.space ×ˢ Ico (0 : ℝ) (eps / 2))) ∧
      (∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
        (G ⟨c z, hmap ⟨z.property.1, z.property.2.1, z.property.2.2.trans hed.le⟩⟩ : X) =
          c (z.val.1, eps / 2 + z.val.2 / 2)) ∧
      ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G x = x := by
  classical
  let B := K.space ×ˢ Icc (0 : ℝ) delta
  let P := K.space ×ˢ Icc (0 : ℝ) eps
  have hPB : P ⊆ B := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hed.le⟩
  let cR : E × ℝ → R := fun z => if hz : z ∈ B then ⟨c z, hmap hz⟩ else x₀
  have hvalue (z : E × ℝ) (hz : z ∈ B) : (cR z : X) = c z := by
    simp only [cR, dif_pos hz]
  have hc : ContinuousOn cR P := IsEmbedding.subtypeVal.continuousOn_iff.mpr
    ((hcPL.continuousOn.mono hPB).congr (fun z hz => hvalue z (hPB hz)))
  have hi : IsEmbedding (fun z : P => cR z) := by
    have hh := (hemb.comp (IsEmbedding.inclusion hPB)).codRestrict R (fun z => hmap (hPB z.property))
    have heq : (fun z : P => cR z) =
        (fun z : P => (⟨c z, hmap (hPB z.property)⟩ : R)) := by
      funext z
      exact Subtype.ext (hvalue z (hPB z.property))
    rw [heq]
    exact hh
  have himage (S : Set (E × ℝ)) (hSB : S ⊆ B) :
      cR '' S = (Subtype.val : R → X) ⁻¹' (c '' S) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (hvalue z (hSB hz)).symm⟩
    · rintro ⟨z, hz, heq⟩
      exact ⟨z, hz, Subtype.ext ((hvalue z (hSB hz)).trans heq)⟩
  have hopen : IsOpen (cR '' (K.space ×ˢ Ico (0 : ℝ) eps)) := by
    rw [himage _ (fun z hz => hPB ⟨hz.1, hz.2.1, hz.2.2.le⟩)]
    exact hopenSmall
  obtain ⟨G, hGi, hGrange, hGval, hGout⟩ :=
    exists_common_collar_compression (K.isCompact_space_of_finite hK) heps cR hc hi hopen
  have hsmall (z : P) :
      (G ⟨c z, hmap (hPB z.property)⟩ : X) = c (z.val.1, eps / 2 + z.val.2 / 2) := by
    have hzEq : cR z = (⟨c z, hmap (hPB z.property)⟩ : R) :=
      Subtype.ext (hvalue z (hPB z.property))
    have hh := congrArg Subtype.val (hGval z z.property)
    rw [hzEq, hvalue _] at hh
    · exact hh
    · exact ⟨z.property.1, by constructor <;> linarith [z.property.2.1, z.property.2.2]⟩
  have hout (x : R) (hx : (x : X) ∉ c '' P) : G x = x := by
    apply hGout x
    rwa [himage P hPB]
  refine ⟨G, hGi, chartwisePL_common_collar_compression e he K hK heps hed c hcPL
    hemb hmap hopenLarge hfront G hsmall hout, ?_, hsmall, hout⟩
  have hsmallB : K.space ×ˢ Ico (0 : ℝ) (eps / 2) ⊆ B := by
    intro z hz
    exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  rw [himage _ hsmallB] at hGrange
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(G y).property, hGrange.subset (mem_range_self y)⟩
  · intro hx
    obtain ⟨y, hy⟩ := hGrange.symm.subset (show (⟨x, hx.1⟩ : R) ∉
      (Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) (eps / 2))) from hx.2)
    exact ⟨y, congrArg Subtype.val hy⟩

end PoincareConjecture.M76
