import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.StageProjectionWords
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OrdinaryMarkedProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.BoundaryTermination
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedTermination










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1




theorem Step.exists_marked_projection_with_self_paired_components
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)} [Jgroup.Normal]
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ (initial : StageMarkedDisk t R Fmark base Jgroup)
      (g : V2 → s.Carrier) (rim : C(Q2, Fmark))
      (basepath : Path base (rim squareRimBase))
      (model : OrdinaryDoubleCurveModel s.charts g (s.projection ⁻¹' R)),
      Nonempty (OrdinaryDoubleCurveModel s.charts
        (step.projection ∘ step.inclusion ∘ initial.map) (s.projection ⁻¹' R)) ∧
      PolyhedralPLInCharts s.charts g D2 ∧ MapsTo g D2 (s.projection ⁻¹' R) ∧
      (∀ x : Q2, s.projection (g x) = (rim x : M)) ∧
      (∀ x ∈ D2, s.projection (g x) ∈ Fmark ↔ x ∈ Q2) ∧
      (∀ x ∈ D2, g x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Q2) ∧
      basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ Jgroup ∧
      doubleBoundaryComponentCount g D2 Q2 = 0 ∧
      doubleInteriorComponentCount g D2 Q2 ≤
        doubleInteriorComponentCount (step.projection ∘ step.inclusion ∘ initial.map) D2 Q2 ∧
      IsEmbedding (fun x : Q2 ↦ g x) ∧ ∀ i, model.mate i = i := by
  classical
  obtain ⟨initial, ⟨model⟩⟩ := step.exists_ordinary_marked_projection he hF hopen old
  let d : V2 → s.Carrier := step.projection ∘ step.inclusion ∘ initial.map
  let Rs := s.projection ⁻¹' R
  let Fs := s.projection ⁻¹' Fmark
  have hd : PolyhedralPLInCharts s.charts d D2 :=
    initial.piecewiseAffine.project step.chartIndex
      (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ ↦ congrFun (step.chart_forward k) x)
  have horiginal (x : V2) : s.projection (d x) = t.projection (initial.map x) :=
    (step.original_eq (initial.map x)).symm
  have hin : MapsTo d D2 Rs := by
    intro x hx
    change s.projection (d x) ∈ R
    rw [horiginal]
    exact initial.inside hx
  have hfront : ∀ x ∈ D2, d x ∈ frontier Rs ↔ x ∈ Q2 := by
    intro x hx
    rw [show frontier Rs = s.projection ⁻¹' frontier R from s.frontier_region R]
    change s.projection (d x) ∈ frontier R ↔ x ∈ Q2
    rw [horiginal]
    have h := initial.whole_boundary_iff ⟨x, hx⟩
    rwa [t.frontier_region R] at h
  have heS : PoincareConjecture.M76.PLDomain s.charts Rs :=
    ⟨s.cover, s.compatible, he.closed.preimage s.projection.continuous,
      s.halfspace_boundary he.halfspace⟩
  have hFS : Fs ⊆ frontier Rs := by
    rw [show frontier Rs = s.projection ⁻¹' frontier R from s.frontier_region R]
    exact preimage_mono hF
  have hFopen : IsOpen ((Subtype.val : frontier Rs → s.Carrier) ⁻¹' Fs) := by
    let q : frontier Rs → frontier R := fun x ↦
      ⟨s.projection x, (s.frontier_region R).subset x.property⟩
    have hq : Continuous q :=
      (s.projection.continuous.comp continuous_subtype_val).subtype_mk _
    exact hopen.preimage hq
  have hboundary (x : Q2) : s.projection (d x) = (initial.rim x : M) :=
    (horiginal x).trans (initial.boundary_values x)
  have hboundaryS (x : Q2) : d x ∈ Fs := by
    change s.projection (d x) ∈ Fmark
    rw [hboundary x]
    exact (initial.rim x).property
  let rimS : C(Q2, Fs) :=
    ⟨fun x ↦ ⟨d x, hboundaryS x⟩,
      (hd.continuousOn.comp_continuous continuous_subtype_val
        (fun x ↦ sphere_subset_closedBall x.property)).subtype_mk hboundaryS⟩
  let projection : C(Fs, Fmark) :=
    ⟨fun x ↦ ⟨s.projection x, x.property⟩,
      (s.projection.continuous.comp continuous_subtype_val).subtype_mk
        (fun x : Fs ↦ x.property)⟩
  have hprojection (x : Q2) : projection (rimS x) = initial.rim x :=
    Subtype.ext (hboundary x)
  let baseS : Fs := rimS squareRimBase
  have hbase : projection baseS = initial.rim squareRimBase := hprojection squareRimBase
  let q : Path base (projection baseS) := initial.basepath.cast rfl hbase
  let Φ := markedProjectionHom projection q
  let Js : Subgroup (FundamentalGroup Fs baseS) := Jgroup.comap Φ
  let : Js.Normal := Subgroup.normal_comap Φ
  have hout : (Path.refl baseS).whiskeredLoopClass
      (squareRimLoop.map rimS.continuous) ∉ Js := by
    intro h
    change Φ ((Path.refl baseS).whiskeredLoopClass (squareRimLoop.map rimS.continuous)) ∈ Jgroup at h
    rw [markedProjectionHom_refl_whiskered] at h
    have hloop : (squareRimLoop.map rimS.continuous).map projection.continuous =
        (squareRimLoop.map initial.rim.continuous).cast hbase hbase := by
      ext u
      exact congrArg Subtype.val (hprojection (squareRimLoop u))
    rw [hloop] at h
    change (initial.basepath.cast rfl hbase).whiskeredLoopClass
      ((squareRimLoop.map initial.rim.continuous).cast hbase hbase) ∈ Jgroup at h
    rw [whiskeredLoopClass_cast_rim] at h
    exact initial.outside h
  obtain ⟨a, rimA, pathA, ha, haR, haRim, _haF, haFront, haOut,
    haZero, haCount, ⟨modelA⟩, _haEmbedding⟩ :=
    model.exists_marked_disk_without_boundary_double_curves hd heS hFS hFopen rimS
      (fun _ ↦ rfl) (Path.refl baseS) hout hin hfront
  obtain ⟨g, modelG, hg, hgR, hgRim, hgFront, hgBoundary, hgCount, hgSelf⟩ :=
    modelA.exists_disk_without_paired_interior_circles ha heS haR haFront
  have hgZero : doubleBoundaryComponentCount g D2 Q2 = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact hgBoundary.trans_eq haZero
  have hgBoundaryValues (x : Q2) : g x = (rimA x : s.Carrier) :=
    (hgRim x.property).trans (haRim x)
  let rim : C(Q2, Fmark) := projection.comp rimA
  let path : Path base (rim squareRimBase) := q.trans (pathA.map projection.continuous)
  have hword : Φ (pathA.whiskeredLoopClass (squareRimLoop.map rimA.continuous)) =
      path.whiskeredLoopClass (squareRimLoop.map rim.continuous) := by
    rw [markedProjectionHom_whiskered]
    rfl
  have hglobalOut : path.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ Jgroup := by
    intro h
    apply haOut
    change Φ (pathA.whiskeredLoopClass (squareRimLoop.map rimA.continuous)) ∈ Jgroup
    rwa [hword]
  refine ⟨initial, g, rim, path, modelG, ⟨model⟩, hg, hgR, ?_, ?_, hgFront,
    hglobalOut, hgZero, hgCount.trans haCount,
    modelG.isEmbedding_rim_of_boundary_count_zero hg.continuousOn hgZero, ?_⟩
  · intro x
    rw [hgBoundaryValues x]
    rfl
  · intro x hx
    constructor
    · intro h
      exact (hgFront x hx).mp (hFS h)
    · intro hq
      have hv := hgBoundaryValues ⟨x, hq⟩
      change g x ∈ Fs
      rw [hv]
      exact (rimA ⟨x, hq⟩).property
  · intro i
    apply hgSelf i
    apply (modelG.double_locus_disjoint_rim_of_boundary_count_zero hgZero).mono_left
    intro x hx
    exact modelG.cover.subset (mem_iUnion.mpr ⟨i, hx⟩)

end Geometry.OriginalPLTower
