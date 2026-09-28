import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.BoundaryLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.RegionMapExtension

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem exists_original_collar_attached_cylinder
    {E Z X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (x₀ : R)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (HB : K.space ≃ₜ frontier R)
    (c : E × ℝ → X) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) 1))
    (hi : InjOn c (K.space ×ˢ Icc (0 : ℝ) 1))
    (hm : MapsTo c (K.space ×ˢ Icc (0 : ℝ) 1) R)
    (hb : ∀ z : K.space, c (z, 0) = HB z)
    (hp : ∀ z ∈ K.space ×ˢ Icc (0 : ℝ) 1, c z ∈ frontier R ↔ z.2 = 0)
    (G : C(R, R)) (hGi : Function.Injective G) (hGPL : ChartwisePLMap e e G)
    (hGlevel : ∀ z : K.space, (G ⟨c (z, 0), hm ⟨z.property, by norm_num⟩⟩ : X) = c (z, a))
    (hGgap : ∀ x : R, (G x : X) ∉ c '' (K.space ×ˢ Ico (0 : ℝ) a))
    (hGint : ∀ x : R, (G x : X) ∈ interior R)
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    (f : ℝ × Z → X) (hf : PolyhedralPLInCharts e f (Icc (-1 : ℝ) 1 ×ˢ A.space))
    (hfi : InjOn f (Icc (-1 : ℝ) 1 ×ˢ A.space))
    (hfR : MapsTo f (Icc (-1 : ℝ) 1 ×ˢ A.space) R)
    (hfB : ∀ (b : Bool) z, z ∈ A.space → f (if b then 1 else -1, z) ∈ frontier R) :
    ∃ (rim : Bool → Z → E) (g : ℝ × Z → X),
      (∀ b, FinitePiecewiseAffineOn (rim b) A.space) ∧
      (∀ b, MapsTo (rim b) A.space K.space) ∧
      (∀ b z, z ∈ A.space → c (rim b z, 0) = f (if b then 1 else -1, z)) ∧
      PolyhedralPLInCharts e g (Icc (-2 : ℝ) 2 ×ˢ A.space) ∧
      InjOn g (Icc (-2 : ℝ) 2 ×ˢ A.space) ∧
      MapsTo g (Icc (-2 : ℝ) 2 ×ˢ A.space) R ∧
      (∀ z ∈ Icc (-2 : ℝ) 2 ×ˢ A.space, g z ∈ frontier R ↔ z.1 = -2 ∨ z.1 = 2) ∧
      (∀ (b : Bool) z, z ∈ A.space → g (if b then 2 else -2, z) = f (if b then 1 else -1, z)) ∧
      (g '' (Icc (-2 : ℝ) 2 ×ˢ A.space)) ∩ (c '' (K.space ×ˢ Ico (0 : ℝ) a)) =
        c '' (((rim false '' A.space) ∪ (rim true '' A.space)) ×ˢ Ico (0 : ℝ) a) := by
  have hends : ∀ b : Bool, PolyhedralPLInCharts e (fun z => f (if b then 1 else -1, z)) A.space := by
    intro b
    let p : Z →ᴬ[ℝ] (ℝ × Z) :=
      (ContinuousAffineMap.const ℝ Z (if b then 1 else -1)).prod (ContinuousAffineMap.id ℝ Z)
    exact hf.comp_finitePiecewiseAffineOn A hA
      ((A.affineOnFaces_affine p).finitePiecewiseAffineOn hA)
      (fun z hz => ⟨by cases b <;> norm_num, hz⟩)
  have hrims : ∀ b : Bool, ∃ rim : Z → E, FinitePiecewiseAffineOn rim A.space ∧
      MapsTo rim A.space K.space ∧ ∀ z ∈ A.space, c (rim z, 0) = f (if b then 1 else -1, z) :=
    fun b => exists_original_collar_boundary_lift he.compatible HB (by norm_num) c hc hi hb
      A hA _ (hends b) (fun z hz => hfB b z hz)
  choose rim hrim hrimK hrimb using hrims
  let H := extendRegionMap G
  have hH (x : R) : H x = (G x : X) := extendRegionMap_apply G x
  have hlevel : ∀ b z, z ∈ A.space → H (c (rim b z, 0)) = c (rim b z, a) := by
    intro b z hz
    exact (hH ⟨c (rim b z, 0), hm ⟨hrimK b hz, by norm_num⟩⟩).trans
      (hGlevel ⟨rim b z, hrimK b hz⟩)
  have hgap : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ A.space, H (f z) ∉ c '' (K.space ×ˢ Ico (0 : ℝ) a) := by
    intro z hz
    rw [hH ⟨f z, hfR hz⟩]
    exact hGgap _
  have hint : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ A.space, H (f z) ∈ interior R := by
    intro z hz
    rw [hH ⟨f z, hfR hz⟩]
    exact hGint _
  obtain ⟨M, hM, hMs⟩ := exists_finite_interval_cylinder A hA (show (-1 : ℝ) < 1 by norm_num)
  have hmid : PolyhedralPLInCharts e (H ∘ f) (Icc (-1 : ℝ) 1 ×ˢ A.space) :=
    hMs ▸ hGPL.polyhedralPLInCharts_extendRegionMap M hM x₀ f (hMs.symm ▸ hf)
      (fun _ hz => hfR (hMs.subset hz))
  have hsub : K.space ×ˢ Icc (0 : ℝ) a ⊆ K.space ×ˢ Icc (0 : ℝ) 1 :=
    fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans ha1⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK ha
  have hcsmall : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) a) :=
    hJs ▸ hc.restrict_finite J hJ (hJs.subset.trans hsub)
  let g := commonCollarAttachment c rim H f a
  refine ⟨rim, g, hrim, hrimK, hrimb,
    polyhedralPLInCharts_commonCollarAttachment he.compatible c rim A hA ha hcsmall
      hrim hrimK H f hmid hrimb hlevel,
    commonCollarAttachment_injOn c rim ha (hi.mono hsub) hrimK H
      (extendRegionMap_injective hGi) f hfi hrimb hlevel hgap,
    commonCollarAttachment_mapsTo c rim ha (hm.mono_left hsub) hrimK H f
      (fun _ hz => interior_subset (hint _ hz)), ?_, ?_,
    commonCollarAttachment_image_in_open_strip c rim ha (hi.mono hsub) hrimK H f hgap⟩
  · intro z hz
    exact commonCollarAttachment_boundary_iff c rim ha (fun w hw => hp w (hsub hw)) hrimK H f
      (fun w hw => disjoint_interior_frontier.notMem_of_mem_left (hint w hw)) hz
  · intro b z hz
    exact (commonCollarAttachment_end c rim H f a b z).trans (hrimb b z hz)

end PoincareConjecture.M76
