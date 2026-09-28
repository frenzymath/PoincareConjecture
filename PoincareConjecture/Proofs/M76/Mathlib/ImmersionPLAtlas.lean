import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false

open Set Geometry

namespace IsLocalHomeomorph

theorem exists_piecewiseAffine_coordinate_cover
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {f : X → E} (hf : IsLocalHomeomorph f) :
    ∃ c : X → OpenPartialHomeomorph X E,
      (∀ x, x ∈ (c x).source) ∧
      (∀ i, EqOn (c i) f (c i).source) ∧
      (∀ i j, EqOn ((c i).symm.trans (c j)) id ((c i).symm.trans (c j)).source) ∧
      ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E := by
  classical
  choose c hc heq using hf
  have htrans (i j : X) : EqOn ((c i).symm.trans (c j)) id
      ((c i).symm.trans (c j)).source := by
    intro x hx
    change c j ((c i).symm x) = x
    rw [← heq j, heq i]
    exact (c i).right_inv hx.1
  refine ⟨c, hc, fun i _ _ => (congrFun (heq i) _).symm, htrans, ?_⟩
  intro i j
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E)
    ((c i).symm.trans (c j)).open_source).congr (htrans i j).symm

theorem exists_piecewiseAffine_chartedSpace
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {f : X → E} (hf : IsLocalHomeomorph f) :
    ∃ (c : X → OpenPartialHomeomorph X E)
      (hcover : ∀ x, ∃ i, x ∈ (c i).source),
      (∀ i, EqOn (c i) f (c i).source) ∧
      (letI := ChartedSpace.ofChartCover c hcover
       HasGroupoid X (piecewiseAffineGroupoid E)) := by
  obtain ⟨c, hc, hfval, _, hPL⟩ := hf.exists_piecewiseAffine_coordinate_cover
  let hcover : ∀ x, ∃ i, x ∈ (c i).source := fun x => ⟨x, hc x⟩
  exact ⟨c, hcover, hfval, ChartedSpace.hasGroupoid_ofChartCover c hcover _ hPL⟩

end IsLocalHomeomorph

namespace IsLocalHomeomorphOn

theorem isLocalHomeomorph_domRestrict
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {U : Set X} (hf : IsLocalHomeomorphOn f U) (hU : IsOpen U) :
    IsLocalHomeomorph (fun x : U => f x) := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact hf.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
    (fun x _ => x.property)

theorem exists_piecewiseAffine_chartedSpace_domRestrict
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {f : X → E} {U : Set X} (hf : IsLocalHomeomorphOn f U) (hU : IsOpen U) :
    ∃ (c : U → OpenPartialHomeomorph U E)
      (hcover : ∀ x, ∃ i, x ∈ (c i).source),
      (∀ i, EqOn (c i) (fun x : U => f x) (c i).source) ∧
      (letI := ChartedSpace.ofChartCover c hcover
       HasGroupoid U (piecewiseAffineGroupoid E)) :=
  (hf.isLocalHomeomorph_domRestrict hU).exists_piecewiseAffine_chartedSpace

end IsLocalHomeomorphOn
