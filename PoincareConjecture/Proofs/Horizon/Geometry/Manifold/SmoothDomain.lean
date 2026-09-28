import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension










set_option autoImplicit false

open Set
open scoped Manifold ContDiff


theorem ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞}
    {e : OpenPartialHomeomorph M H} {x : M}
    (hk : k ≠ 0) (he : e ∈ IsManifold.maximalAtlas I k M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  have hd : IsLocalDiffeomorphAt I I k e x := by
    refine ⟨{ toPartialEquiv := e.toPartialEquiv
              open_source := e.open_source
              open_target := e.open_target
              contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
              contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he },
      hx, fun _ _ => rfl⟩
  have hi := hd.isInteriorPoint_iff hk
  change I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) at hi
  refine hi.trans ⟨fun h => e.mem_interior_extend_target (e.mapsTo hx) h, fun h => ?_⟩
  exact e.interior_extend_target_subset_interior_range h

namespace Poincare.Manifold



structure SmoothDomain (n : ℕ) [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (Ω : Set M) where
  isOpen : IsOpen Ω
  isConnected : IsConnected Ω
  isCompact_closure : IsCompact (closure Ω)
  chartedSpace : ChartedSpace (EuclideanHalfSpace n) (closure Ω)
  isManifold : letI := chartedSpace; IsManifold (𝓡∂ n) ∞ (closure Ω)
  isSmoothEmbedding : letI := chartedSpace;
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ n) (𝓡 n) ∞
      (Subtype.val : closure Ω → M)
  image_interior : letI := chartedSpace;
    Subtype.val '' (𝓡∂ n).interior (closure Ω) = Ω
  boundary_nonempty : letI := chartedSpace;
    ((𝓡∂ n).boundary (closure Ω)).Nonempty

namespace SmoothDomain

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {Ω : Set M} (D : SmoothDomain n Ω)

include D


def intrinsicInterior : Set (closure Ω) :=
  letI := D.chartedSpace
  (𝓡∂ n).interior (closure Ω)


def intrinsicBoundary : Set (closure Ω) :=
  letI := D.chartedSpace
  (𝓡∂ n).boundary (closure Ω)

theorem intrinsicBoundary_eq_compl : D.intrinsicBoundary = D.intrinsicInteriorᶜ := by
  let := D.chartedSpace
  exact (ModelWithCorners.compl_interior (I := 𝓡∂ n) (M := closure Ω)).symm

@[simp] theorem image_intrinsicInterior : Subtype.val '' D.intrinsicInterior = Ω :=
  D.image_interior


@[simp] theorem image_boundary :
    Subtype.val '' D.intrinsicBoundary = frontier Ω := by
  rw [D.intrinsicBoundary_eq_compl, compl_eq_univ_sdiff,
    Set.image_sdiff Subtype.val_injective, image_univ, Subtype.range_val,
    D.image_intrinsicInterior, D.isOpen.frontier_eq]

@[simp] theorem mem_intrinsicInterior_iff (x : closure Ω) :
    x ∈ D.intrinsicInterior ↔ (x : M) ∈ Ω := by
  have hm := Set.ext_iff.mp D.image_intrinsicInterior (x : M)
  constructor
  · exact fun hx => hm.mp ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hm.mpr hx
    exact Subtype.val_injective hyx ▸ hy

@[simp] theorem mem_intrinsicBoundary_iff (x : closure Ω) :
    x ∈ D.intrinsicBoundary ↔ (x : M) ∈ frontier Ω := by
  rw [← D.image_boundary, Set.mem_image]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact Subtype.val_injective hyx ▸ hy

theorem nonempty : Ω.Nonempty := D.isConnected.nonempty

theorem isCompact_frontier : IsCompact (frontier Ω) :=
  D.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure

theorem frontier_nonempty : (frontier Ω).Nonempty := by
  rw [← D.image_boundary]
  exact D.boundary_nonempty.image Subtype.val

theorem isConnected_closure : IsConnected (closure Ω) := D.isConnected.closure

theorem compactSpace_closure : CompactSpace (closure Ω) :=
  isCompact_iff_compactSpace.mp D.isCompact_closure

theorem connectedSpace_domain : ConnectedSpace Ω :=
  isConnected_iff_connectedSpace.mp D.isConnected

theorem connectedSpace_closure : ConnectedSpace (closure Ω) :=
  isConnected_iff_connectedSpace.mp D.isConnected_closure

theorem contMDiff_inclusion :
    letI := D.chartedSpace
    ContMDiff (𝓡∂ n) (𝓡 n) ∞ (Subtype.val : closure Ω → M) := by
  let := D.chartedSpace
  exact D.isSmoothEmbedding.contMDiff



theorem exists_compatible_charts (x : closure Ω) :
    letI := D.chartedSpace
    ∃ (φ : OpenPartialHomeomorph (closure Ω) (EuclideanHalfSpace n))
      (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
      x ∈ φ.source ∧ (x : M) ∈ ψ.source ∧
      φ ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ (closure Ω) ∧
      ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M ∧
      φ.source ⊆ Subtype.val ⁻¹' ψ.source ∧
      EqOn (ψ ∘ Subtype.val) (A ∘ (𝓡∂ n) ∘ φ) φ.source := by
  let := D.chartedSpace
  have h := D.isSmoothEmbedding.isImmersion.isImmersionAt x
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    h.equiv.toLinearMap.comp (LinearMap.inl ℝ _ _)
  have hL : Function.Injective L := by
    intro u v huv
    exact congrArg Prod.fst (h.equiv.injective huv)
  let A := (LinearEquiv.ofBijective L
    ⟨hL, LinearMap.injective_iff_surjective.mp hL⟩).toContinuousLinearEquiv
  refine ⟨h.domChart, h.codChart, A, h.mem_domChart_source,
    h.mem_codChart_source, h.domChart_mem_maximalAtlas,
    h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  intro y hy
  have hz := h.writtenInCharts
    ((h.domChart.extend (𝓡∂ n)).map_source (by simpa only
      [OpenPartialHomeomorph.extend_source] using hy))
  dsimp only [Function.comp_apply] at hz
  rw [h.domChart.extend_left_inv hy] at hz
  exact hz


theorem exists_flattening_chart (x : closure Ω) :
    ∃ (ψ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
      (x : M) ∈ ψ.source ∧ ψ ∈ IsManifold.maximalAtlas (𝓡 n) ∞ M ∧
      ∀ y ∈ ψ.source,
        (y ∈ closure Ω ↔ 0 ≤ (A.symm (ψ y)) 0) ∧
        (y ∈ Ω ↔ 0 < (A.symm (ψ y)) 0) ∧
        (y ∈ frontier Ω ↔ (A.symm (ψ y)) 0 = 0) := by
  let := D.chartedSpace
  let := D.isManifold
  obtain ⟨φ, ψ, A, hxφ, hxψ, hφ, hψ, hsource, hcoord⟩ := D.exists_compatible_charts x
  obtain ⟨U, hU, hUφ⟩ :=
    D.isSmoothEmbedding.isEmbedding.isInducing.isOpen_iff.mp φ.open_source
  obtain ⟨W, hW, hWφ⟩ :=
    (𝓡∂ n).isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp φ.open_target
  let V := U ∩ (ψ.source ∩ ψ ⁻¹' (A.symm ⁻¹' W))
  have hV : IsOpen V := hU.inter (ψ.isOpen_inter_preimage (hW.preimage A.symm.continuous))
  have hcoord' (z : closure Ω) (hz : z ∈ φ.source) :
      A.symm (ψ z) = (𝓡∂ n) (φ z) := by
    rw [show ψ z = A ((𝓡∂ n) (φ z)) from hcoord hz]
    exact A.symm_apply_apply _
  have hxU : (x : M) ∈ U := by
    change x ∈ Subtype.val ⁻¹' U
    rwa [hUφ]
  have hxW : A.symm (ψ x) ∈ W := by
    rw [hcoord' x hxφ]
    change φ x ∈ (𝓡∂ n) ⁻¹' W
    rw [hWφ]
    exact φ.map_source hxφ
  have hxV : (x : M) ∈ V := ⟨hxU, hxψ, hxW⟩
  refine ⟨ψ.restr V, A, ?_, restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡 n)) hψ hV, ?_⟩
  · rw [ψ.restr_source' V hV]
    exact ⟨hxψ, hxV⟩
  intro y hy
  rw [ψ.restr_source' V hV] at hy
  change (y ∈ closure Ω ↔ 0 ≤ (A.symm (ψ y)) 0) ∧
    (y ∈ Ω ↔ 0 < (A.symm (ψ y)) 0) ∧
    (y ∈ frontier Ω ↔ (A.symm (ψ y)) 0 = 0)
  have hyφ (hyΩ : y ∈ closure Ω) : (⟨y, hyΩ⟩ : closure Ω) ∈ φ.source := by
    rw [← hUφ]
    exact hy.2.1
  have hclosure : y ∈ closure Ω ↔ 0 ≤ (A.symm (ψ y)) 0 := by
    constructor
    · intro hyΩ
      rw [hcoord' ⟨y, hyΩ⟩ (hyφ hyΩ)]
      exact (φ ⟨y, hyΩ⟩).property
    · intro hz
      let z : EuclideanHalfSpace n := ⟨A.symm (ψ y), hz⟩
      have hzφ : z ∈ φ.target := by
        rw [← hWφ]
        exact hy.2.2.2
      have hzin := φ.map_target hzφ
      have heq : ψ (φ.symm z) = ψ y := by
        rw [show ψ (φ.symm z) = A ((𝓡∂ n) (φ (φ.symm z))) from hcoord hzin,
          φ.right_inv hzφ]
        exact A.apply_symm_apply _
      have hval : (φ.symm z : M) = y := ψ.injOn (hsource hzin) hy.1 heq
      exact hval ▸ (φ.symm z).property
  have hinterior : y ∈ Ω ↔ 0 < (A.symm (ψ y)) 0 := by
    by_cases hyΩ : y ∈ closure Ω
    · rw [← D.mem_intrinsicInterior_iff ⟨y, hyΩ⟩]
      change (𝓡∂ n).IsInteriorPoint (⟨y, hyΩ⟩ : closure Ω) ↔ _
      rw [hcoord' ⟨y, hyΩ⟩ (hyφ hyΩ)]
      have hi := ModelWithCorners.isInteriorPoint_iff_of_mem_maximalAtlas
        (I := 𝓡∂ n) (by simp : (∞ : WithTop ℕ∞) ≠ 0) hφ (hyφ hyΩ)
      refine hi.trans ⟨fun h => ?_, fun h => ?_⟩
      · have h' := φ.interior_extend_target_subset_interior_range h
        simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
          interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using h'
      · apply φ.mem_interior_extend_target (φ.mapsTo (hyφ hyΩ))
        rwa [interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
    · exact ⟨fun h => (hyΩ (subset_closure h)).elim,
        fun h => (hyΩ (hclosure.mpr h.le)).elim⟩
  refine ⟨hclosure, hinterior, ?_⟩
  rw [D.isOpen.frontier_eq, mem_sdiff, hclosure, hinterior]
  exact ⟨fun h => le_antisymm (le_of_not_gt h.2) h.1, fun h => by simp [h]⟩


theorem exists_flattening_parametrization (x : closure Ω) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (x : M) ∈ e.target ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ∀ z ∈ e.source,
        (e z ∈ closure Ω ↔ 0 ≤ z 0) ∧
        (e z ∈ Ω ↔ 0 < z 0) ∧
        (e z ∈ frontier Ω ↔ z 0 = 0) := by
  obtain ⟨ψ, A, hx, hψ, hflat⟩ := D.exists_flattening_chart x
  let e := A.toHomeomorph.toOpenPartialHomeomorph.trans ψ.symm
  have hs : e.source = A ⁻¹' ψ.target := by
    simp [e]
  have ht : e.target = ψ.source := by
    simp [e]
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    apply (contMDiffOn_symm_of_mem_maximalAtlas hψ).comp
      (A.contDiff.contMDiff.contMDiffOn) ?_
    intro z hz
    exact hs ▸ hz
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    apply A.symm.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hψ).mono ?_)
    exact ht ▸ Subset.rfl
  refine ⟨e, ht ▸ hx, he, hei, ?_⟩
  intro z hz
  have hzA : A z ∈ ψ.target := by simpa only [hs, mem_preimage] using hz
  have h := hflat (ψ.symm (A z)) (ψ.map_target hzA)
  simpa only [ψ.right_inv hzA, A.symm_apply_apply, e,
    OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph] using h

end SmoothDomain

end Poincare.Manifold
