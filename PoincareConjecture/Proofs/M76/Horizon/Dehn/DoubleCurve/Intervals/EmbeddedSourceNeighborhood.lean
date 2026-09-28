import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_injective_source_open
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {f : V2 → X} {R : Set X} (old : OrdinaryDoubleCurveModel e f R)
    (x : doubleLocusOn f D2) :
    ∃ U : Set D2, IsOpen U ∧ (⟨x, x.property.1⟩ : D2) ∈ U ∧
      InjOn (fun y : D2 ↦ f y) U := by
  obtain ⟨C⟩ := old.crossings x x.property.1 (old.partner x) (old.partner x).property.1
    (Ne.symm (old.partner_free x)) (old.partner_value x).symm
  have hbranch (B : Set V2) (hBo : IsOpen ((Subtype.val : D2 → V2) ⁻¹' B))
      (hBi : IsEmbedding (fun y : B ↦ f y)) (hx : (x : V2) ∈ B) :
      ∃ U : Set D2, IsOpen U ∧ (⟨x, x.property.1⟩ : D2) ∈ U ∧
        InjOn (fun y : D2 ↦ f y) U := by
    refine ⟨Subtype.val ⁻¹' B, hBo, hx, ?_⟩
    intro a ha b hb hab
    exact Subtype.ext (congrArg (Subtype.val : B → V2) (hBi.injective
      (show (fun y : B ↦ f y) ⟨a, ha⟩ = (fun y : B ↦ f y) ⟨b, hb⟩ from hab)))
  rcases C.labels with h | h
  · exact hbranch C.left C.left_open C.left_embedding h.1
  · exact hbranch C.right C.right_open C.right_embedding h.1

theorem OrdinaryDoubleCurveModel.exists_finite_embedded_source_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {A W : Set V2}
    {region : Set X} (old : OrdinaryDoubleCurveModel e f region)
    (hf : PolyhedralPLInCharts e f D2) (hA : IsCompact A)
    (hAG : A ⊆ doubleLocusOn f D2) (hinj : InjOn f A)
    (hW : IsOpen ((Subtype.val : D2 → V2) ⁻¹' W)) (hAW : A ⊆ W) :
    ∃ (P : SimplicialComplex ℝ V2) (U : Set D2),
      P.faces.Finite ∧ P.space ⊆ D2 ∩ W ∧
      IsOpen U ∧ (Subtype.val : D2 → V2) ⁻¹' A ⊆ U ∧
      Subtype.val '' U ⊆ P.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ PolyhedralPLInCharts e f P.space := by
  have hAD : A ⊆ D2 := fun _ hx ↦ (hAG hx).1
  have hAimage : (Subtype.val : D2 → V2) '' ((Subtype.val : D2 → V2) ⁻¹' A) = A :=
    image_preimage_eq_iff.mpr (fun x hx ↦ ⟨⟨x, hAD hx⟩, rfl⟩)
  have hAc : IsCompact ((Subtype.val : D2 → V2) ⁻¹' A) :=
    IsEmbedding.subtypeVal.isCompact_iff.mpr (hAimage.symm ▸ hA)
  have hfc : Continuous (fun x : D2 ↦ f x) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.property)
  have hinj' : InjOn (fun x : D2 ↦ f x) ((Subtype.val : D2 → V2) ⁻¹' A) :=
    fun _ hx _ hy hxy ↦ Subtype.ext (hinj hx hy hxy)
  obtain ⟨V, hVo, hAV, hVi⟩ := hinj'.exists_isOpen_superset hAc
    (fun x _ ↦ hfc.continuousAt) (by
      intro x hx
      obtain ⟨U, hUo, hxU, hUi⟩ := old.exists_injective_source_open ⟨x, hAG hx⟩
      exact ⟨U, hUo.mem_nhds hxU, hUi⟩)
  obtain ⟨O, hOo, hOV⟩ := isOpen_induced_iff.mp (hVo.inter hW)
  have hAO : A ⊆ O := by
    intro x hx
    exact hOV.symm.subset ⟨hAV (show (⟨x, hAD hx⟩ : D2) ∈ Subtype.val ⁻¹' A from hx), hAW hx⟩
  obtain ⟨N, hN, hAN, hNO⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed hA hOo hAO
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Q, hQ, hQs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V2 D2 (sphere (0 : V2) 1))
  obtain ⟨P, hP, hPs⟩ := N.exists_finite_triangulation_inter Q hN hQ
  have hPD : P.space ⊆ D2 := fun _ hx ↦ hQs ▸ (hPs.subset hx).2
  have hPV (x : P.space) : (⟨x, hPD x.property⟩ : D2) ∈ V ∩ Subtype.val ⁻¹' W :=
    hOV.subset (hNO (hPs.subset x.property).1)
  let U : Set D2 := Subtype.val ⁻¹' interior N.space
  have hUi : Subtype.val '' U ⊆ P.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPs.symm.subset ⟨interior_subset hx, hQs.symm ▸ x.property⟩
  have hPL := hf.restrict_finite P hP hPD
  let : CompactSpace P.space := isCompact_iff_compactSpace.mp (P.isCompact_space_of_finite hP)
  refine ⟨P, U, hP, fun x hx ↦ ⟨hPD hx, (hPV ⟨x, hx⟩).2⟩,
    isOpen_interior.preimage continuous_subtype_val, fun x hx ↦ hAN hx, hUi, ?_, hPL⟩
  have hinjP : Function.Injective (fun x : P.space ↦ f x) := by
    intro x y hxy
    exact Subtype.ext (congrArg (Subtype.val : D2 → V2) (hVi (hPV x).1 (hPV y).1 hxy))
  exact ((hPL.continuousOn.comp_continuous continuous_subtype_val
    (fun x ↦ x.property)).isClosedEmbedding hinjP).isEmbedding

end PoincareConjecture.M76.Dehn
