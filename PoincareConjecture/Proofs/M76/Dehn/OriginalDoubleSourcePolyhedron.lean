import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleRelation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DoubleRelationProjection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProjectedEmbedding
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_finite_double_source_polyhedron
    {s t : Stage e S f r C} (step : Step s t)
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space => j x)) :
    ∃ (L : SimplicialComplex ℝ (V2 × V2)) (G : SimplicialComplex ℝ V2)
      (H : L.space ≃ₜ G.space),
      L.faces.Finite ∧ G.faces.Finite ∧
      L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        step.projection (step.inclusion (j z.1)) =
          step.projection (step.inclusion (j z.2)) ∧ z.1 ≠ z.2} ∧
      G.space = {x | x ∈ K.space ∧ ∃ y ∈ K.space, x ≠ y ∧
        step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j y))} ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ ∀ z : L.space, (H z : V2) = z.val.1 := by
  obtain ⟨L, hL, hLs⟩ := step.exists_finite_projected_double_complex K hK hj hji
  let p : K.space → s.Carrier := fun x => step.projection (step.inclusion (j x))
  have hupper : Function.Injective (fun x : K.space => step.inclusion (j x)) :=
    step.openEmbedding.isEmbedding.injective.comp hji.injective
  have hfiber (y : s.Carrier) : (p ⁻¹' {y}).Finite ∧ (p ⁻¹' {y}).ncard ≤ 2 := by
    have hfinite : (step.projection ⁻¹' {y}).Finite :=
      finite_of_ncard_pos (by rw [step.two y]; norm_num)
    have hbound := hupper.finite_fiber_comp_ncard_le hfinite
    exact ⟨hbound.1, hbound.2.trans_eq (step.two y)⟩
  have hfirst : InjOn Prod.fst L.space := by
    intro z hz w hw heq
    rw [hLs] at hz hw
    let z' : K.space × K.space := (⟨z.1, hz.1⟩, ⟨z.2, hz.2.1⟩)
    let w' : K.space × K.space := (⟨w.1, hw.1⟩, ⟨w.2, hw.2.1⟩)
    have hzw : z' = w' := Function.injOn_fst_double_relation (f := p)
      (fun y => (hfiber y).1) (fun y => (hfiber y).2)
      ⟨hz.2.2.1, fun h => hz.2.2.2 (congrArg Subtype.val h)⟩
      ⟨hw.2.2.1, fun h => hw.2.2.2 (congrArg Subtype.val h)⟩
      (Subtype.ext heq)
    exact Prod.ext heq (congrArg (fun q : K.space × K.space => (q.2 : V2)) hzw)
  let first : V2 × V2 →ᴬ[ℝ] V2 := (ContinuousLinearMap.fst ℝ V2 V2).toContinuousAffineMap
  have hfaces := L.affineOnFaces_affine first
  let G := hfaces.embeddedImage hfirst
  have hG : G.faces.Finite := hfaces.embeddedImage_finite hfirst hL
  have hGs : G.space = Prod.fst '' L.space := hfaces.embeddedImage_space hfirst
  have hPL := hfaces.finitePiecewiseAffineOn hL
  obtain ⟨H₀, hH₀, hH₀val⟩ := hPL.exists_homeomorph_image hfirst
  let H : L.space ≃ₜ G.space := H₀.trans (Homeomorph.setCongr hGs.symm)
  have hH : H.IsFinitePL := hH₀.trans (Homeomorph.isFinitePL_setCongr hGs.symm G hG hGs)
  refine ⟨L, G, H, hL, hG, hLs, ?_, hH, hH.symm, hH₀val⟩
  rw [hGs, hLs]
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz.1, z.2, hz.2.1, hz.2.2.2, hz.2.2.1⟩
  · rintro ⟨hx, y, hy, hne, heq⟩
    exact ⟨(x, y), ⟨hx, hy, heq, hne⟩, rfl⟩

end Geometry.OriginalPLTower
