import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.FiniteCarrier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph



set_option autoImplicit false
open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_paired_intersection_source_carriers
    {E F V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f K.space) (hg : PolyhedralPLInCharts e g L.space)
    (hfi : InjOn f K.space) (hgi : InjOn g L.space) :
    ∃ (A : SimplicialComplex ℝ E) (B : SimplicialComplex ℝ F) (H : A.space ≃ₜ B.space),
      A.faces.Finite ∧ B.faces.Finite ∧
      A.space = {x | x ∈ K.space ∧ f x ∈ g '' L.space} ∧
      B.space = {y | y ∈ L.space ∧ g y ∈ f '' K.space} ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ (∀ x : A.space, f x = g (H x)) ∧
      f '' A.space = f '' K.space ∩ g '' L.space ∧
      g '' B.space = f '' K.space ∩ g '' L.space := by
  classical
  obtain ⟨R, hR, hRs⟩ := hf.exists_finite_common_value_complex he K L hK hL hg
  have hfirst : InjOn Prod.fst R.space := by
    intro z hz w hw hzw
    obtain ⟨hzK, hzL, hzg⟩ := hRs.subset hz
    obtain ⟨hwK, hwL, hwg⟩ := hRs.subset hw
    exact Prod.ext hzw (hgi hzL hwL (hzg.symm.trans ((congrArg f hzw).trans hwg)))
  have hsecond : InjOn Prod.snd R.space := by
    intro z hz w hw hzw
    obtain ⟨hzK, hzL, hzg⟩ := hRs.subset hz
    obtain ⟨hwK, hwL, hwg⟩ := hRs.subset hw
    exact Prod.ext (hfi hzK hwK (hzg.trans ((congrArg g hzw).trans hwg.symm))) hzw
  let first : E × F →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap
  let second : E × F →ᴬ[ℝ] F := (ContinuousLinearMap.snd ℝ E F).toContinuousAffineMap
  have hfaces₀ := R.affineOnFaces_affine first
  have hfaces₁ := R.affineOnFaces_affine second
  let A := hfaces₀.embeddedImage hfirst
  let B := hfaces₁.embeddedImage hsecond
  have hA : A.faces.Finite := hfaces₀.embeddedImage_finite hfirst hR
  have hB : B.faces.Finite := hfaces₁.embeddedImage_finite hsecond hR
  have hAs : A.space = Prod.fst '' R.space := hfaces₀.embeddedImage_space hfirst
  have hBs : B.space = Prod.snd '' R.space := hfaces₁.embeddedImage_space hsecond
  obtain ⟨H₀, hH₀, hH₀val⟩ := (hfaces₀.finitePiecewiseAffineOn hR).exists_homeomorph_image hfirst
  obtain ⟨H₁, hH₁, hH₁val⟩ := (hfaces₁.finitePiecewiseAffineOn hR).exists_homeomorph_image hsecond
  let A₀ : R.space ≃ₜ A.space := H₀.trans (Homeomorph.setCongr hAs.symm)
  let B₀ : R.space ≃ₜ B.space := H₁.trans (Homeomorph.setCongr hBs.symm)
  have hA₀ : A₀.IsFinitePL := hH₀.trans (Homeomorph.isFinitePL_setCongr hAs.symm A hA hAs)
  have hB₀ : B₀.IsFinitePL := hH₁.trans (Homeomorph.isFinitePL_setCongr hBs.symm B hB hBs)
  have hAval (z : R.space) : (A₀ z : E) = z.val.1 := hH₀val z
  have hBval (z : R.space) : (B₀ z : F) = z.val.2 := hH₁val z
  let H := A₀.symm.trans B₀
  have hH : H.IsFinitePL := hA₀.symm.trans hB₀
  have hAwhole : A.space = {x | x ∈ K.space ∧ f x ∈ g '' L.space} := by
    rw [hAs, hRs]
    ext x
    constructor
    · rintro ⟨z, ⟨hzK, hzL, heq⟩, rfl⟩
      exact ⟨hzK, z.2, hzL, heq.symm⟩
    · rintro ⟨hxK, y, hyL, heq⟩
      exact ⟨(x, y), ⟨hxK, hyL, heq.symm⟩, rfl⟩
  have hBwhole : B.space = {y | y ∈ L.space ∧ g y ∈ f '' K.space} := by
    rw [hBs, hRs]
    ext y
    constructor
    · rintro ⟨z, ⟨hzK, hzL, heq⟩, rfl⟩
      exact ⟨hzL, z.1, hzK, heq⟩
    · rintro ⟨hyL, x, hxK, heq⟩
      exact ⟨(x, y), ⟨hxK, hyL, heq⟩, rfl⟩
  refine ⟨A, B, H, hA, hB, hAwhole, hBwhole, hH, hH.symm, ?_, ?_, ?_⟩
  · intro x
    have heq := (hRs.subset (A₀.symm x).property).2.2
    have hx : (A₀.symm x).val.1 = (x : E) :=
      (hAval (A₀.symm x)).symm.trans (congrArg Subtype.val (A₀.apply_symm_apply x))
    change f x = g (B₀ (A₀.symm x))
    rw [hBval, ← hx]
    exact heq
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_image_of_mem f (hAwhole.subset hy).1, (hAwhole.subset hy).2⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, hAwhole.symm.subset ⟨hy, hx⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hBwhole.subset hy).2, mem_image_of_mem g (hBwhole.subset hy).1⟩
    · rintro ⟨hx, y, hy, rfl⟩
      exact ⟨y, hBwhole.symm.subset ⟨hy, hx⟩, rfl⟩

end Geometry
