import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Dehn.OriginalPLSuccessor
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

universe v w z a

open Set Metric Topology Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem protectedAnnulus_pathConnectedSpace : PathConnectedSpace ProtectedAnnulus.source := by
  let : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, le_rfl, zero_le_one⟩)
  let : PathConnectedSpace Q2 :=
    surjective_squareRimLoop.pathConnectedSpace squareRimLoop.continuous
  exact ProtectedAnnulus.cylinder.surjective.pathConnectedSpace
    ProtectedAnnulus.cylinder.continuous

variable {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → M} {r : M → ℝ} {C : Set M}

theorem exists_annulus_step_of_two_sheet_cover
    (s : Stage e S f r C) (hS : S.faces.Finite)
    (hsource : S.space = ProtectedAnnulus.source)
    (v0 : S.space) (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    {Y : Type a} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    {p : Y → s.Carrier} (hp : IsCoveringMap p)
    (htwo : ∀ x, (p ⁻¹' {x}).ncard = 2)
    (negative : C(Q2, Y))
    (hnegative : ∀ u : Q2,
      p (negative u) = s.sourceMap (ProtectedAnnulus.endpoint false, u)) :
    ∃ t : Stage e S f r C, Nonempty (Step s t) := by
  let : PathConnectedSpace ProtectedAnnulus.source := protectedAnnulus_pathConnectedSpace
  let : PathConnectedSpace S.space :=
    (Homeomorph.setCongr hsource).symm.surjective.pathConnectedSpace
      (Homeomorph.setCongr hsource).symm.continuous
  obtain ⟨top, b, hb, hT2, hconn, hcover, htwo'⟩ := hp.exists_two_sheet_model htwo
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
  let negative' : C(Q2, s.Carrier × Fin 2) :=
    ⟨fun u ↦ b.symm (negative u), b.symm.continuous.comp negative.continuous⟩
  have hnegative' (u : Q2) :
      p' (negative' u) = s.sourceMap (ProtectedAnnulus.endpoint false, u) := by
    have h := hb (b.symm (negative u))
    rw [b.apply_symm_apply] at h
    exact h.symm.trans (hnegative u)
  obtain ⟨g, hg, hpg, _⟩ := ProtectedAnnulus.exists_polyhedralPL_source_lift hcover c
    (fun i x ↦ (hccenter i x).mpr)
    (fun k x _ ↦ congrFun (hcval k) x) (hsource ▸ s.sourcePL) negative' hnegative'
  have hg : PolyhedralPLInCharts c g S.space := hsource.symm ▸ hg
  have hpg : EqOn (p' ∘ g) s.sourceMap S.space := hsource.symm ▸ hpg
  have hrUp : ∀ k, LocallyPiecewiseAffineOn ((r ∘ Q) ∘ (c k).symm) (c k).target := by
    intro k
    apply ((s.cutPL hrPL k.1).mono (c k).open_target (hctarget k)).congr
    intro y hy
    exact congrArg (r ∘ s.projection) (hcinv k hy).symm
  obtain ⟨z, _, _, _, _, _, _, _, hlevel⟩ :=
    OpenPartialHomeomorph.exists_polyhedral_image_open_cut_deformation c hccompat hccover
      S hS hg isOpen_univ (fun _ _ ↦ mem_univ _) (hr.comp Q.continuous) hrUp
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
      (fun x hx ↦ hAO (mem_image_of_mem g hx))
  let j : C(O, s.Carrier × Fin 2) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(O, M) := Q.comp j
  have hinv (k) : EqOn ((P ∘ j) ∘ (d k).symm)
      (s.charts k.1.1).symm (d k).target := by
    intro y hy
    exact (congrArg p' (hdinv k hy)).trans (hcinv k.1 (hdtarget k hy))
  have htarget (k) : (d k).target ⊆ (s.charts k.1.1).target :=
    (hdtarget k).trans (hctarget k.1)
  let H' : (ContinuousMap.id O).HomotopyRel a (g' '' S.space) :=
    { H.toHomotopy with prop' := fun t _ hx ↦ H.eq_fst t (himage.subset hx) }
  let t : Stage e S f r C :=
    { Carrier := O
      Index := (s.Index × (s.Carrier × Fin 2)) × O
      charts := d
      cover := hdcover
      compatible := hdcompat
      projection := q
      projectionLocal := s.projectionLocal.comp
        (hcover.isLocalHomeomorph.comp hO.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
      projection_mem := fun x ↦ s.projection_mem (p' x)
      chartIndex := fun k ↦ s.chartIndex k.1.1
      chart_target := fun k ↦ (htarget k).trans (s.chart_target k.1.1)
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
      source_eq := fun x hx ↦
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
    source_eq := fun _ hx ↦ (congrArg p' (hgf hx)).trans (hpg hx)
    original_eq := fun _ ↦ rfl
    chartIndex := fun k ↦ k.1.1
    chart_target := htarget
    chart_forward := ?_
    chart_inverse := hinv }⟩⟩
  intro k
  rw [hdval k, hcval k.1]
  rfl

end Geometry.OriginalPLTower
