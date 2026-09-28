import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProjectedDoubleLocus
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DoubleRelationProjection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProjectedEmbedding
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_finite_surface_double_source_polyhedron
    {s t : Stage e S f r C} (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space => j x)) :
    ∃ (L : SimplicialComplex ℝ (V × V)) (G : SimplicialComplex ℝ V)
      (H : L.space ≃ₜ G.space),
      L.faces.Finite ∧ G.faces.Finite ∧
      L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        step.projection (step.inclusion (j z.1)) =
          step.projection (step.inclusion (j z.2)) ∧ z.1 ≠ z.2} ∧
      G.space = {x | x ∈ K.space ∧ ∃ y ∈ K.space, x ≠ y ∧
        step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j y))} ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ ∀ z : L.space, (H z : V) = z.val.1 := by
  obtain ⟨_, _, L, _, hL, _, hLs, _⟩ := step.exists_finite_source_double_locus K hK hj hji
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
    have hz' : p z'.1 = p z'.2 ∧ z'.1 ≠ z'.2 :=
      ⟨hz.2.2.1, fun h => hz.2.2.2 (congrArg Subtype.val h)⟩
    have hw' : p w'.1 = p w'.2 ∧ w'.1 ≠ w'.2 :=
      ⟨hw.2.2.1, fun h => hw.2.2.2 (congrArg Subtype.val h)⟩
    have hzw : z' = w' := Function.injOn_fst_double_relation (f := p)
      (fun y => (hfiber y).1) (fun y => (hfiber y).2)
      hz' hw'
      (Subtype.ext heq)
    exact Prod.ext heq (congrArg (fun q : K.space × K.space => (q.2 : V)) hzw)
  let first : V × V →ᴬ[ℝ] V := (ContinuousLinearMap.fst ℝ V V).toContinuousAffineMap
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
