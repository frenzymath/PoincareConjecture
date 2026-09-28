import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoSheetCoverModel
import PoincareConjecture.Proofs.M76.Mathlib.CoveringPLSuccessor
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover











set_option autoImplicit false

universe u v w z a

open Set Topology Geometry unitInterval

namespace Geometry.OriginalPLTower

variable {U : Type u} {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}




structure Step (s t : Stage e S f r C) where
  Cover : Type w
  [topology : TopologicalSpace Cover]
  [t2 : T2Space Cover]
  [connected : ConnectedSpace Cover]
  projection : C(Cover, s.Carrier)
  covering : IsCoveringMap projection
  two : ∀ x, (projection ⁻¹' {x}).ncard = 2
  inclusion : C(t.Carrier, Cover)
  openEmbedding : IsOpenEmbedding inclusion
  source_eq : ∀ x ∈ S.space,
    projection (inclusion (t.sourceMap x)) = s.sourceMap x
  original_eq : ∀ x, t.projection x = s.projection (projection (inclusion x))
  chartIndex : t.Index → s.Index
  chart_target : ∀ k, (t.charts k).target ⊆ (s.charts (chartIndex k)).target
  chart_forward : ∀ k, (t.charts k : t.Carrier → E) =
    (s.charts (chartIndex k)) ∘ projection ∘ inclusion
  chart_inverse : ∀ k, EqOn
    ((projection ∘ inclusion) ∘ (t.charts k).symm)
    (s.charts (chartIndex k)).symm (t.charts k).target

attribute [instance] Step.topology Step.t2 Step.connected



theorem Step.chart_source {s t : Stage e S f r C} (step : Step s t) (k : t.Index) :
    MapsTo (step.projection ∘ step.inclusion) (t.charts k).source
      (s.charts (step.chartIndex k)).source := by
  intro x hx
  have hz := (t.charts k).map_source hx
  have hi := step.chart_inverse k hz
  have he := (s.charts (step.chartIndex k)).map_target (step.chart_target k hz)
  change step.projection (step.inclusion ((t.charts k).symm (t.charts k x))) =
    (s.charts (step.chartIndex k)).symm (t.charts k x) at hi
  rw [(t.charts k).left_inv hx] at hi
  change step.projection (step.inclusion x) ∈ (s.charts (step.chartIndex k)).source
  exact hi.symm ▸ he



def Reaches (s t : Stage e S f r C) : Prop :=
  Relation.ReflTransGen (fun a b => Nonempty (Step a b)) s t





theorem exists_step_of_two_sheet_cover [FiniteDimensional ℝ U]
    (s : Stage e S f r C) (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    (v0 : S.space) (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    {Y : Type a} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    {p : Y → s.Carrier} (hp : IsCoveringMap p)
    (htwo : ∀ x, (p ⁻¹' {x}).ncard = 2) :
    ∃ t : Stage e S f r C, Nonempty (Step s t) := by
  obtain ⟨top, _, _, hT2, hconn, hcover, htwo'⟩ := hp.exists_two_sheet_model htwo
  let : TopologicalSpace (s.Carrier × Fin 2) := top
  let : T2Space (s.Carrier × Fin 2) := hT2
  let : ConnectedSpace (s.Carrier × Fin 2) := hconn
  let p' : s.Carrier × Fin 2 → s.Carrier := Prod.fst
  let P : C(s.Carrier × Fin 2, s.Carrier) := ⟨p', hcover.continuous⟩
  let Q : C(s.Carrier × Fin 2, M) := s.projection.comp P
  obtain ⟨c, hccover, hccenter, _, hctarget, hcval, hcinv, hccompat⟩ :=
    hcover.isLocalHomeomorph.exists_piecewiseAffine_coordinate_cover_over
      s.charts s.cover s.compatible
  let := ChartedSpace.ofChartCover c hccover
  let : LocallyCompactSpace (s.Carrier × Fin 2) :=
    ChartedSpace.locallyCompactSpace E (s.Carrier × Fin 2)
  obtain ⟨g, _, hpg, hg⟩ := hcover.exists_polyhedralPL_lift c
    (fun i x => (hccenter i x).mpr)
    (fun k x _ => congrFun (hcval k) x) S hS s.sourcePL
    v0 (s.sourceMap v0, 0) rfl
  have hrUp : ∀ k, LocallyPiecewiseAffineOn ((r ∘ Q) ∘ (c k).symm) (c k).target := by
    intro k
    apply ((s.cutPL hrPL k.1).mono (c k).open_target (hctarget k)).congr
    intro y hy
    exact congrArg (r ∘ s.projection) (hcinv k hy).symm
  obtain ⟨z, _, _, _, _, _, _, _, hlevel⟩ :=
    OpenPartialHomeomorph.exists_polyhedral_image_open_cut_deformation c hccompat hccover
      S hS hg isOpen_univ (fun _ _ => mem_univ _) (hr.comp Q.continuous) hrUp
  obtain ⟨_, hO, hAO, _, _, a, H, ha, hpos, hzero, _⟩ :=
    hlevel (1 / 2) (by norm_num) (by norm_num)
  let O : Set (s.Carrier × Fin 2) := {x | (1 : ℝ) / 2 < z x}
  have hA : IsPathConnected (g '' S.space) := by
    simpa only [range_domRestrict] using isPathConnected_range hg.continuousOn.domRestrict
  have hpath : PathConnectedSpace O := by
    apply H.toHomotopy.pathConnectedSpace_of_range
    rw [ha]
    exact hA.preimage_coe hAO
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let : PathConnectedSpace O := hpath
  obtain ⟨d, g', hdcover, hdcompat, hdtarget, hdval, hdinv, hg', hgf, himage⟩ :=
    hg.exists_open_restriction hccover hccompat S hS v0 hO
      (fun x hx => hAO (mem_image_of_mem g hx))
  let j : C(O, s.Carrier × Fin 2) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(O, M) := Q.comp j
  have hinv (k) : EqOn ((P ∘ j) ∘ (d k).symm)
      (s.charts k.1.1).symm (d k).target := by
    intro y hy
    exact (congrArg p' (hdinv k hy)).trans (hcinv k.1 (hdtarget k hy))
  have htarget (k) : (d k).target ⊆ (s.charts k.1.1).target :=
    (hdtarget k).trans (hctarget k.1)
  let H' : (ContinuousMap.id O).HomotopyRel a (g' '' S.space) :=
    { H.toHomotopy with prop' := fun t _ hx => H.eq_fst t (himage.subset hx) }
  let t : Stage e S f r C :=
    { Carrier := O
      Index := (s.Index × (s.Carrier × Fin 2)) × O
      charts := d
      cover := hdcover
      compatible := hdcompat
      projection := q
      projectionLocal := s.projectionLocal.comp
        (hcover.isLocalHomeomorph.comp hO.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
      projection_mem := fun x => s.projection_mem (p' x)
      chartIndex := fun k => s.chartIndex k.1.1
      chart_target := fun k => (htarget k).trans (s.chart_target k.1.1)
      chart_forward := by
        intro k
        rw [hdval k, hcval k.1, s.chart_forward k.1.1]
        rfl
      chart_inverse := by
        intro k y hy
        exact (congrArg s.projection (hinv k hy)).trans
          (s.chart_inverse k.1.1 (htarget k hy))
      sourceMap := g'
      sourcePL := hg'
      source_eq := fun x hx =>
        (congrArg s.projection ((congrArg p' (hgf hx)).trans (hpg hx))).trans
          (s.source_eq x hx)
      endpoint := a
      deformation := H'
      endpoint_range := ha.trans himage.symm
      nonneg_preserved := hpos
      zero_preserved := hzero }
  refine ⟨t, ⟨{
    Cover := s.Carrier × Fin 2
    projection := P
    covering := hcover
    two := htwo'
    inclusion := j
    openEmbedding := hO.isOpenEmbedding_subtypeVal
    source_eq := fun _ hx => (congrArg p' (hgf hx)).trans (hpg hx)
    original_eq := fun _ => rfl
    chartIndex := fun k => k.1.1
    chart_target := htarget
    chart_forward := ?_
    chart_inverse := hinv }⟩⟩
  intro k
  rw [hdval k, hcval k.1]
  rfl

end Geometry.OriginalPLTower
