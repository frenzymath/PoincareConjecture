import PoincareConjecture.Proofs.M83.PositiveLocalOrientation
import PoincareConjecture.Proofs.M83.LocalOrientationGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

private abbrev ChartIndex (M : Type) [TopologicalSpace M]
    (P : PositiveThreeAtlas M) :=
  {e : OpenPartialHomeomorph M E3 // e ∈ P.charts.atlas}

private def chartSet {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i : ChartIndex M P) : Set M := i.1.source

private def chartMap {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i : ChartIndex M P) :
    C(chartSet i, E3) :=
  ⟨fun z => i.1 z, by exact i.1.continuousOn.domRestrict⟩

private def chartInclusion {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i : ChartIndex M P) :
    C(chartSet i, M) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def overlapSet {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) : Set M :=
  chartSet i ∩ chartSet j

private def overlapToChart {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) :
    C(overlapSet i j, chartSet i) :=
  ⟨fun z => ⟨z.1, z.2.1⟩,
    continuous_subtype_val.subtype_mk _⟩

private def overlapToChart' {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) :
    C(overlapSet i j, chartSet j) :=
  ⟨fun z => ⟨z.1, z.2.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private theorem overlap_open {M : Type} [TopologicalSpace M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) :
    IsOpen (overlapSet i j) :=
  i.1.open_source.inter j.1.open_source

private theorem overlap_to_chart_openEmbedding
    {M : Type} [TopologicalSpace M] [T2Space M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) :
    _root_.Topology.IsOpenEmbedding (overlapToChart i j) := by
  apply (i.1.open_source.isOpenEmbedding_subtypeVal).of_comp
    (overlapToChart i j)
  change _root_.Topology.IsOpenEmbedding
    ((chartInclusion i).comp (overlapToChart i j))
  change _root_.Topology.IsOpenEmbedding
    ((overlapSet i j).domRestrict (fun z : M => z))
  exact (overlap_open i j).isOpenEmbedding_subtypeVal

private theorem overlap_to_chart'_openEmbedding
    {M : Type} [TopologicalSpace M] [T2Space M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P) :
    _root_.Topology.IsOpenEmbedding (overlapToChart' i j) := by
  apply (j.1.open_source.isOpenEmbedding_subtypeVal).of_comp
    (overlapToChart' i j)
  change _root_.Topology.IsOpenEmbedding
    ((chartInclusion j).comp (overlapToChart' i j))
  change _root_.Topology.IsOpenEmbedding
    ((overlapSet i j).domRestrict (fun z : M => z))
  exact (overlap_open i j).isOpenEmbedding_subtypeVal

private theorem chart_overlap_orientation
    {M : Type} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    {P : PositiveThreeAtlas M} (i j : ChartIndex M P)
    [LocallyCompactSpace (chartSet i)] [LocallyCompactSpace (chartSet j)]
    [LocallyCompactSpace (overlapSet i j)]
    (x : M) (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    let W := overlapSet i j
    let z : W := ⟨x, hi, hj⟩
    ((euclideanLocalOrientation.pullback (chartMap i)
      i.1.isOpenEmbedding_restrict).pullback (overlapToChart i j)
        (overlap_to_chart_openEmbedding i j)).atPoint z =
    ((euclideanLocalOrientation.pullback (chartMap j)
        j.1.isOpenEmbedding_restrict).pullback (overlapToChart' i j)
          (overlap_to_chart'_openEmbedding i j)).atPoint z := by
  let W := overlapSet i j
  let z : W := ⟨x, hi, hj⟩
  let wi := overlapToChart i j
  let wj := overlapToChart' i j
  let ci := (chartMap i).comp wi
  let cj := (chartMap j).comp wj
  have hwi : _root_.Topology.IsOpenEmbedding wi :=
    overlap_to_chart_openEmbedding i j
  have hwj : _root_.Topology.IsOpenEmbedding wj :=
    overlap_to_chart'_openEmbedding i j
  have hci : _root_.Topology.IsOpenEmbedding ci := by
    change _root_.Topology.IsOpenEmbedding ((chartMap i) ∘ wi)
    exact i.1.isOpenEmbedding_restrict.comp hwi
  have hcj : _root_.Topology.IsOpenEmbedding cj := by
    change _root_.Topology.IsOpenEmbedding ((chartMap j) ∘ wj)
    exact j.1.isOpenEmbedding_restrict.comp hwj
  have hleft :
      ((euclideanLocalOrientation.pullback (chartMap i)
        i.1.isOpenEmbedding_restrict).pullback wi hwi).atPoint z =
      (euclideanLocalOrientation.pullback ci hci).atPoint z := by
    simpa [ci] using
      (LocalOrientation.pullback_comp euclideanLocalOrientation wi (chartMap i)
        hwi i.1.isOpenEmbedding_restrict z)
  let d : OpenPartialHomeomorph E3 E3 := j.1.symm.trans i.1
  let : LocallyCompactSpace d.source := d.open_source.locallyCompactSpace
  have hdpoint : j.1 x ∈ d.source := by
    change j.1 x ∈ j.1.target ∩ j.1.symm ⁻¹' i.1.source
    exact ⟨j.1.map_source hj, by
      change j.1.symm (j.1 x) ∈ i.1.source
      rw [j.1.left_inv hj]
      exact hi⟩
  let dinc : C(d.source, E3) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hqmem (w : W) : j.1 w.1 ∈ d.source := by
    change j.1 w.1 ∈ j.1.target ∩ j.1.symm ⁻¹' i.1.source
    exact ⟨j.1.map_source w.2.2, by
      change j.1.symm (j.1 w.1) ∈ i.1.source
      rw [j.1.left_inv w.2.2]
      exact w.2.1⟩
  let q : C(W, d.source) :=
    ⟨fun w => ⟨j.1 w.1, hqmem w⟩,
      ((chartMap j).continuous.comp wj.continuous).subtype_mk hqmem⟩
  have hq : _root_.Topology.IsOpenEmbedding q := by
    apply d.open_source.isOpenEmbedding_subtypeVal.of_comp q
    change _root_.Topology.IsOpenEmbedding (dinc.comp q)
    change _root_.Topology.IsOpenEmbedding cj
    exact hcj
  let dmap : C(d.source, E3) :=
    ⟨d.source.domRestrict d, d.continuousOn.domRestrict⟩
  have hdmap : _root_.Topology.IsOpenEmbedding dmap := d.isOpenEmbedding_restrict
  have hfactor : ci = dmap.comp q := by
    ext z : 1
    change i.1 z.1 = d (j.1 z.1)
    change i.1 z.1 = i.1 (j.1.symm (j.1 z.1))
    rw [j.1.left_inv z.2.2]
  have hsource : dinc.comp q = cj := by
    ext z
    rfl
  have hright_orientation :
      ((euclideanLocalOrientation.pullback (chartMap j)
        j.1.isOpenEmbedding_restrict).pullback wj hwj).atPoint z =
      ((euclideanLocalOrientation.pullback dinc
        d.open_source.isOpenEmbedding_subtypeVal).pullback q hq).atPoint z := by
    have h := LocalOrientation.pullback_comp euclideanLocalOrientation q dinc
      hq d.open_source.isOpenEmbedding_subtypeVal z
    exact (LocalOrientation.pullback_comp euclideanLocalOrientation wj (chartMap j)
      hwj j.1.isOpenEmbedding_restrict z).trans h.symm
  have hdet : 0 < (fderiv Real (fun y : E3 => d y)
      (j.1 x)).toLinearMap.det := by
    simpa [d] using P.positive_transition j.1 i.1 j.2 i.2 x ⟨hj, hi⟩
  have hpositive := positiveOpenPartialOrientation euclideanLocalOrientation d
    ⟨j.1 x, hdpoint⟩ hdet
  have hfactor_orientation :
      (euclideanLocalOrientation.pullback ci hci).atPoint z =
        ((euclideanLocalOrientation.pullback dmap hdmap).pullback q hq).atPoint z :=
    (LocalOrientation.pullback_congr euclideanLocalOrientation ci (dmap.comp q)
      hci (hdmap.comp hq) hfactor z).trans
      (LocalOrientation.pullback_comp euclideanLocalOrientation q dmap hq hdmap z).symm
  have hpositive_pullback :
      ((euclideanLocalOrientation.pullback dmap hdmap).pullback q hq).atPoint z =
      ((euclideanLocalOrientation.pullback dinc
        d.open_source.isOpenEmbedding_subtypeVal).pullback q hq).atPoint z := by
    apply (localHomologyEquiv q hq z 3).injective
    change localHomologyMap q hq.injective z 3 _ = localHomologyMap q hq.injective z 3 _
    rw [LocalOrientation.map_pullback, LocalOrientation.map_pullback]
    exact hpositive
  have hlocal :
      ((euclideanLocalOrientation.pullback (chartMap i)
        i.1.isOpenEmbedding_restrict).pullback wi hwi).atPoint z =
      ((euclideanLocalOrientation.pullback (chartMap j)
        j.1.isOpenEmbedding_restrict).pullback wj hwj).atPoint z := by
    exact hleft.trans (hfactor_orientation.trans
      (hpositive_pullback.trans hright_orientation.symm))
  exact hlocal

theorem exists_localOrientation_of_positiveThreeAtlas
    {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [Nonempty M]
    (P : PositiveThreeAtlas M) :
    Nonempty (LocalOrientation M) := by
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) M := P.charts
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) M
  let I := ChartIndex M P
  let U : I → Set M := fun i => chartSet i
  let O : ∀ i : I, LocalOrientation (U i) := fun i => by
    letI : LocallyCompactSpace (U i) := i.1.open_source.locallyCompactSpace
    exact euclideanLocalOrientation.pullback (chartMap i)
      i.1.isOpenEmbedding_restrict
  have hU : ∀ i : I, IsOpen (U i) := by
    intro i
    exact i.1.open_source
  have hcover : ∀ x : M, ∃ i : I, x ∈ U i := by
    intro x
    let e : I := ⟨P.charts.chartAt x, P.charts.chart_mem_atlas x⟩
    exact ⟨e, P.charts.mem_chart_source x⟩
  have hcompat : ∀ (i j : I) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
      (O i).inclusionClass ⟨x, hi⟩ = (O j).inclusionClass ⟨x, hj⟩ := by
    intro i j x hi hj
    let W := overlapSet i j
    let z : W := ⟨x, hi, hj⟩
    let : LocallyCompactSpace (U i) := i.1.open_source.locallyCompactSpace
    let : LocallyCompactSpace (U j) := j.1.open_source.locallyCompactSpace
    let : LocallyCompactSpace W := (overlap_open i j).locallyCompactSpace
    let wi := overlapToChart i j
    let wj := overlapToChart' i j
    let hwi : _root_.Topology.IsOpenEmbedding wi :=
      overlap_to_chart_openEmbedding i j
    let hwj : _root_.Topology.IsOpenEmbedding wj :=
      overlap_to_chart'_openEmbedding i j
    let incW : C(W, M) := ⟨Subtype.val, continuous_subtype_val⟩
    let hincW : _root_.Topology.IsOpenEmbedding incW :=
      (overlap_open i j).isOpenEmbedding_subtypeVal
    have hinc_i : Function.Injective (chartInclusion i) := by
      intro a b hab
      exact Subtype.ext hab
    have hinc_j : Function.Injective (chartInclusion j) := by
      intro a b hab
      exact Subtype.ext hab
    have hcomp_i : (chartInclusion i).comp wi = incW := by
      ext w
      rfl
    have hcomp_j : (chartInclusion j).comp wj = incW := by
      ext w
      rfl
    have hli := congrArg
      (fun k => k (((O i).pullback wi hwi).atPoint z))
      (localHomologyMap_comp wi (chartInclusion i) hwi.injective hinc_i z 3)
    have hlj := congrArg
      (fun k => k (((O j).pullback wj hwj).atPoint z))
      (localHomologyMap_comp wj (chartInclusion j) hwj.injective hinc_j z 3)
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hli
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hlj
    have hmap_i : localHomologyMap ((chartInclusion i).comp wi)
          (hinc_i.comp hwi.injective) z 3 (((O i).pullback wi hwi).atPoint z) =
        localHomologyMap incW hincW.injective z 3 (((O i).pullback wi hwi).atPoint z) := by
      cases hcomp_i
      rfl
    have hmap_j : localHomologyMap ((chartInclusion j).comp wj)
          (hinc_j.comp hwj.injective) z 3 (((O j).pullback wj hwj).atPoint z) =
        localHomologyMap incW hincW.injective z 3 (((O j).pullback wj hwj).atPoint z) := by
      cases hcomp_j
      rfl
    have hlocal := chart_overlap_orientation i j x hi hj
    have hli' : (O i).inclusionClass ⟨x, hi⟩ =
        localHomologyMap incW hincW.injective z 3 (((O i).pullback wi hwi).atPoint z) := by
      simpa [LocalOrientation.inclusionClass, incW, chartInclusion, wi,
        overlapToChart, z] using hli.trans hmap_i
    have hlj' : (O j).inclusionClass ⟨x, hj⟩ =
        localHomologyMap incW hincW.injective z 3 (((O j).pullback wj hwj).atPoint z) := by
      simpa [LocalOrientation.inclusionClass, incW, chartInclusion, wj,
        overlapToChart', z] using hlj.trans hmap_j
    have hmaps := congrArg (fun q => localHomologyMap incW hincW.injective z 3 q) hlocal
    exact hli'.trans (hmaps.trans hlj'.symm)
  exact ⟨LocalOrientation.glue U hU O hcover hcompat⟩

theorem exists_localOrientation_of_orientationCompatibleAtlas
    {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [Nonempty M]
    (A : PoincareConjecture.OrientationCompatibleAtlas M) :
    Nonempty (LocalOrientation M) := by
  exact exists_localOrientation_of_positiveThreeAtlas
    (positiveThreeAtlasOfSigned M A)

end PoincareConjecture.Proofs.M83
