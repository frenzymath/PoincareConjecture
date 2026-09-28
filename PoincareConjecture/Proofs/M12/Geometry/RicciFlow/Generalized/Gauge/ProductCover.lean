import PoincareConjecture.Definitions.M12GaugeCover
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def ordinaryProductChartOpen (x : M) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x).target,
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target⟩

def ordinaryProductChartInverse
    (x : M) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (ordinaryProductChartOpen (n := n) x) M ∞ := by
  classical
  let pe : PartialEquiv (ordinaryProductChartOpen (n := n) x) M :=
    { toFun := fun z : ordinaryProductChartOpen x ↦
        (chartAt (EuclideanSpace ℝ (Fin n)) x).symm z
      invFun := fun y : M ↦
        if hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source then
          ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x) y,
              by simpa [ordinaryProductChartOpen] using
                (chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hy⟩
        else
          ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x) x,
            by simpa [ordinaryProductChartOpen] using
              (chartAt (EuclideanSpace ℝ (Fin n)) x).map_source
                (mem_chart_source (EuclideanSpace ℝ (Fin n)) x)⟩
      source := Set.univ
      target := (chartAt (EuclideanSpace ℝ (Fin n)) x).source
      map_source' := by
        intro z hz
        exact (chartAt (EuclideanSpace ℝ (Fin n)) x).symm.map_source z.property
      map_target' := by
        intro y hy
        exact Set.mem_univ _
      left_inv' := by
        intro z hz
        apply Subtype.ext
        split
        · rename_i hy
          change (chartAt (EuclideanSpace ℝ (Fin n)) x)
              ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm (z : EuclideanSpace ℝ (Fin n))) = z
          exact (chartAt (EuclideanSpace ℝ (Fin n)) x).right_inv z.property
        · rename_i hy
          exact False.elim (hy ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm.map_source z.property))
      right_inv' := by
        intro y hy
        simp only [dif_pos hy]
        exact (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hy
      }
  let result : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (ordinaryProductChartOpen (n := n) x) M ∞ :=
    { toPartialEquiv := pe
      open_source := isOpen_univ
      open_target := (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
      contMDiffOn_toFun := by
        intro z hz
        change ContMDiffWithinAt (𝓡 n) (𝓡 n) ∞
          (fun w : ordinaryProductChartOpen (n := n) x ↦
            (chartAt (EuclideanSpace ℝ (Fin n)) x).symm w)
          Set.univ z
        rw [contMDiffWithinAt_univ, contMDiffAt_subtype_iff]
        exact (contMDiffOn_chart_symm (x := x)).contMDiffAt
          ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds z.property)
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff (I := 𝓡 n) (I' := 𝓡 n)
          (ordinaryProductChartOpen (n := n) x) pe.invFun pe.target y).mp
        apply ((contMDiffOn_chart (I := 𝓡 n) (n := ∞) (x := x)).contMDiffAt
          ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hy)
          |>.contMDiffWithinAt).congr
        · intro z hz
          simpa [pe, Function.comp_def, ordinaryProductChartOpen, dif_pos hz]
        · simpa [pe, Function.comp_def, ordinaryProductChartOpen, dif_pos hy] }
  exact result

def ordinaryProductSourceMap {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (x : M) :
    D.Point × ordinaryProductChartOpen (n := n) x → D.Point × M :=
  fun p => (p.1, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm p.2)

def ordinaryProductSourcePartial {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (x : M) :
    PartialDiffeomorph (spacetimeModel n) (spacetimeModel n)
      (D.Point × ordinaryProductChartOpen (n := n) x) (D.Point × M) ∞ := by
  let e₁ : PartialDiffeomorph (𝓡∂ 1) (𝓡∂ 1) D.Point D.Point ∞ :=
    (Diffeomorph.refl (𝓡∂ 1) D.Point ∞).toPartialDiffeomorph
  let e₂ := ordinaryProductChartInverse (n := n) x
  let result : PartialDiffeomorph (spacetimeModel n) (spacetimeModel n)
      (D.Point × ordinaryProductChartOpen (n := n) x) (D.Point × M) ∞ :=
    { toPartialEquiv := e₁.toPartialEquiv.prod e₂.toPartialEquiv
      open_source := by
        change IsOpen ((Set.univ : Set D.Point) ×ˢ
          (Set.univ : Set (ordinaryProductChartOpen (n := n) x)))
        exact (isOpen_univ : IsOpen (Set.univ : Set D.Point)).prod
          (isOpen_univ : IsOpen (Set.univ : Set (ordinaryProductChartOpen (n := n) x)))
      open_target := by
        change IsOpen ((Set.univ : Set D.Point) ×ˢ
          (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
        exact (isOpen_univ : IsOpen (Set.univ : Set D.Point)).prod
          (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
      contMDiffOn_toFun := by
        change ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞
          (Prod.map (e₁ : D.Point → D.Point)
            (e₂ : ordinaryProductChartOpen (n := n) x → M))
          (e₁.source ×ˢ e₂.source)
        exact e₁.contMDiffOn_toFun.prodMap e₂.contMDiffOn_toFun
      contMDiffOn_invFun := by
        change ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞
          (Prod.map (e₁.invFun : D.Point → D.Point)
            (e₂.invFun : M → ordinaryProductChartOpen (n := n) x))
          (e₁.target ×ˢ e₂.target)
        exact e₁.contMDiffOn_invFun.prodMap e₂.contMDiffOn_invFun }
  exact result

theorem ordinaryProductSourceMap_localDiffeomorph {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (x : M) :
    IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞
      (ordinaryProductSourceMap (n := n) D x) := by
  intro p
  refine ⟨ordinaryProductSourcePartial (n := n) D x, ?_, ?_⟩
  · exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  · intro q hq
    rfl

theorem ordinaryProductSourceMap_injective {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (x : M) :
    Function.Injective (ordinaryProductSourceMap (n := n) D x) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun z : D.Point × M => z.1) hpq
  apply Subtype.ext
  exact (chartAt (EuclideanSpace ℝ (Fin n)) x).symm.injOn
    p.2.property q.2.property (congrArg Prod.snd hpq)

def OrdinaryProductSpacetimeConclusion.chartCylinder
    {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}
    (P : OrdinaryProductSpacetimeConclusion g I) (x : M) :
    CompatibleSpacetimeCylinder P.spacetime (P.timeIntervals.interval I)
      (ordinaryProductChartOpen (n := n) x) := by
  let D := P.timeIntervals.interval I
  let f := ordinaryProductSourceMap (n := n) D x
  have hf := ordinaryProductSourceMap_localDiffeomorph (n := n) D x
  have hlocal : IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞
      (P.productIdentification ∘ f) := by
    intro p
    exact (hf p).comp _ _ (P.productIdentification.isLocalDiffeomorph (f p))
  refine
    { interval_subset := Set.Subset.refl _
      toSpacetime := P.productIdentification ∘ f
      embedding := ?_
      time_eq := ?_
      worldline_smooth := ?_
      worldline_derivative := ?_
      smooth := hlocal.contMDiff
      differential_injective := fun p =>
        ((hlocal p).mfderivToContinuousLinearEquiv (by simp)).injective }
  · exact P.productIdentification.toHomeomorph.isEmbedding.comp
      (hf.isLocalHomeomorph.isOpenEmbedding_of_injective
        (ordinaryProductSourceMap_injective (n := n) D x)).isEmbedding
  · intro p
    change (P.productIdentification (f p)).1.val = p.1.val
    rw [P.productIdentification_eq]
    rfl
  · intro y
    exact hlocal.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  · intro t y
    have heq : (P.productIdentification : D.Point × M → P.spacetime.Point) =
        P.productCylinder.toSpacetime := by
      funext p
      exact (P.productIdentification_eq p).trans (P.productCylinder_eq p).symm
    dsimp only [Function.comp_def, f, ordinaryProductSourceMap]
    rw [heq]
    exact P.productCylinder.worldline_derivative t
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)

theorem OrdinaryProductSpacetimeConclusion.chartCylinder_localDiffeomorph
    {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}
    (P : OrdinaryProductSpacetimeConclusion g I) (x : M) :
    IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞
      (P.chartCylinder x).toSpacetime := by
  intro p
  exact (ordinaryProductSourceMap_localDiffeomorph (n := n) _ x p).comp _ _
    (P.productIdentification.isLocalDiffeomorph _)

def OrdinaryProductSpacetimeConclusion.gaugeCover
    {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}
    (P : OrdinaryProductSpacetimeConclusion g I) :
    SpacetimeGaugeCover P.spacetime P.timeIntervals where
  index := M
  interval _ := I
  spatial := ordinaryProductChartOpen
  cylinder := P.chartCylinder
  metric x := (P.coordinate_compatible.cylinder_metric _ I (P.chartCylinder x)).some
  local_diffeomorph := P.chartCylinder_localDiffeomorph
  covers p := by
    let x := p.2
    let y : ordinaryProductChartOpen (n := n) x :=
      ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x) x,
        (chartAt (EuclideanSpace ℝ (Fin n)) x).map_source
          (mem_chart_source (EuclideanSpace ℝ (Fin n)) x)⟩
    refine ⟨x, (p.1, y), ?_⟩
    change P.productIdentification (p.1,
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm y) = p
    rw [P.productIdentification_eq]
    apply Prod.ext
    · rfl
    exact (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) x)

end
end PoincareConjecture
