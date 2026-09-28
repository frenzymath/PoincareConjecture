import PoincareConjecture.Proofs.M76.Wall.CompactMetrizableNeighborhood
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceBoundaryPullback
import PoincareConjecture.Proofs.M76.Wall.ActualCutDomains
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Local.Homeomorph



set_option autoImplicit false
open Set Geometry Topology
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem PLDomain.exists_oriented_metrizable_neighborhood
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (O : LocalOrientation X) :
    ∃ N : Set X, IsOpen N ∧ R ⊆ N ∧ TopologicalSpace.MetrizableSpace N ∧
      ∃ d : ι × N → OpenPartialHomeomorph N V3,
        PLDomain d ((Subtype.val : N → X) ⁻¹' R) ∧
        (∀ i x, x ∈ (d (i, x)).source ↔ (x : X) ∈ (e i).source) ∧
        (∀ k, MapsTo (Subtype.val : N → X) (d k).source (e k.1).source) ∧
        (∀ k, (d k).target ⊆ (e k.1).target) ∧
        (∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val) ∧
        (∀ k, EqOn ((Subtype.val : N → X) ∘ (d k).symm)
          (e k.1).symm (d k).target) ∧
        frontier ((Subtype.val : N → X) ⁻¹' R) =
          (Subtype.val : N → X) ⁻¹' frontier R ∧
        interior ((Subtype.val : N → X) ⁻¹' R) =
          (Subtype.val : N → X) ⁻¹' interior R ∧
        IsCompact ((Subtype.val : N → X) ⁻¹' R) ∧
        ∃ O' : LocalOrientation N,
          IsLocalOrientationLift (Subtype.val : N → X) O O' := by
  obtain ⟨N, hN, hRN, _, hmetric⟩ :=
    OpenPartialHomeomorph.exists_metrizable_open_neighborhood e he.cover he.compatible
      hR isOpen_univ (subset_univ R)
  have hv : IsLocalHomeomorph (Subtype.val : N → X) :=
    hN.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  obtain ⟨d, hdcover, hdcenter, hdsource, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hv.exists_piecewiseAffine_coordinate_cover_over e he.cover he.compatible
  have hd : PLDomain d ((Subtype.val : N → X) ⁻¹' R) :=
    ⟨hdcover, hdcompat, he.closed.preimage hv.continuous,
      hv.halfspace_boundary_preimage e d Prod.fst hdtarget hdinv he.halfspace⟩
  have hfront : frontier ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' frontier R :=
    (hv.isOpenMap.preimage_frontier_eq_frontier_preimage hv.continuous R).symm
  have hint : interior ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' interior R :=
    (hv.isOpenMap.preimage_interior_eq_interior_preimage hv.continuous R).symm
  have hcompact : IsCompact ((Subtype.val : N → X) ⁻¹' R) :=
    IsInducing.subtypeVal.isCompact_preimage' hR (by simpa only [Subtype.range_coe] using hRN)
  let := ChartedSpace.ofChartCover e he.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  let : LocallyCompactSpace N := hN.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨O', hO'⟩ := exists_localOrientation_lift_of_isLocalHomeomorph
    (Subtype.val : N → X) hv O
  exact ⟨N, hN, hRN, hmetric, d, hd, hdcenter, hdsource, hdtarget,
    hdval, hdinv, hfront, hint, hcompact, O', hO'⟩



theorem exists_original_parameter_in_neighborhood
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R N : Set X}
    (hRN : R ⊆ N) (d : ι × N → OpenPartialHomeomorph N V3)
    (hcenter : ∀ i x, x ∈ (d (i, x)).source ↔ (x : X) ∈ (e i).source)
    (hval : ∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val)
    (hfront : frontier ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' frontier R)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (x₀ : K.space)
    (f : E → X) (hf : PolyhedralPLInCharts e f K.space)
    (hfi : InjOn f K.space) (hfR : MapsTo f K.space R) :
    ∃ g : E → N, PolyhedralPLInCharts d g K.space ∧ InjOn g K.space ∧
      MapsTo g K.space ((Subtype.val : N → X) ⁻¹' R) ∧
      EqOn ((Subtype.val : N → X) ∘ g) f K.space ∧
      g '' K.space = (Subtype.val : N → X) ⁻¹' (f '' K.space) ∧
      ∀ x ∈ K.space, g x ∈ frontier ((Subtype.val : N → X) ⁻¹' R) ↔
        f x ∈ frontier R := by
  classical
  let g (x : E) : N := if hx : x ∈ K.space then ⟨f x, hRN (hfR hx)⟩
    else ⟨f x₀, hRN (hfR x₀.property)⟩
  have hgf : EqOn ((Subtype.val : N → X) ∘ g) f K.space := by
    intro x hx
    simp only [Function.comp_apply, g, dif_pos hx]
  have hgc : ContinuousOn g K.space := by
    apply IsEmbedding.subtypeVal.continuousOn_iff.mpr
    exact hf.continuousOn.congr (fun x hx => hgf hx)
  have hg : PolyhedralPLInCharts d g K.space := hf.lift d
    (fun i x => (hcenter i x).mpr) (fun k x _ => congrFun (hval k) x)
    K hK hgc hgf
  refine ⟨g, hg, ?_, ?_, hgf, ?_, ?_⟩
  · intro x hx y hy hxy
    apply hfi hx hy
    exact (hgf hx).symm.trans ((congrArg Subtype.val hxy).trans (hgf hy))
  · intro x hx
    change (Subtype.val ∘ g) x ∈ R
    rw [hgf hx]
    exact hfR hx
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hgf hx).symm⟩
    · rintro ⟨x, hx, hxz⟩
      exact ⟨x, hx, Subtype.ext ((hgf hx).trans hxz)⟩
  · intro x hx
    rw [hfront]
    change (Subtype.val ∘ g) x ∈ frontier R ↔ f x ∈ frontier R
    rw [hgf hx]

end PoincareConjecture.M76
