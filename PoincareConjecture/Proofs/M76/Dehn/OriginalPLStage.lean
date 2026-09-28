import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceBoundaryPullback
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralImageOpenDeformation
import PoincareConjecture.Proofs.M76.Mathlib.OpenSubtypePLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.HomotopyConnectedRange











set_option autoImplicit false

universe u v w z

open Set Topology Geometry unitInterval

namespace Geometry.OriginalPLTower

variable {U : Type u} {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]





structure Stage (e : ι → OpenPartialHomeomorph M E)
    (S : SimplicialComplex ℝ U) (f : U → M) (r : M → ℝ) (C : Set M) where
  Carrier : Type w
  [topology : TopologicalSpace Carrier]
  [t2 : T2Space Carrier]
  [locallyCompact : LocallyCompactSpace Carrier]
  [pathConnected : PathConnectedSpace Carrier]
  Index : Type (max w z)
  charts : Index → OpenPartialHomeomorph Carrier E
  cover : ∀ x, ∃ k, x ∈ (charts k).source
  compatible : ∀ k l, (charts k).symm.trans (charts l) ∈ piecewiseAffineGroupoid E
  projection : C(Carrier, M)
  projectionLocal : IsLocalHomeomorph projection
  projection_mem : ∀ x, projection x ∈ C
  chartIndex : Index → ι
  chart_target : ∀ k, (charts k).target ⊆ (e (chartIndex k)).target
  chart_forward : ∀ k, (charts k : Carrier → E) = e (chartIndex k) ∘ projection
  chart_inverse : ∀ k,
    EqOn (projection ∘ (charts k).symm) (e (chartIndex k)).symm (charts k).target
  sourceMap : U → Carrier
  sourcePL : PolyhedralPLInCharts charts sourceMap S.space
  source_eq : ∀ x ∈ S.space, projection (sourceMap x) = f x
  endpoint : C(Carrier, Carrier)
  deformation : (ContinuousMap.id Carrier).HomotopyRel endpoint (sourceMap '' S.space)
  endpoint_range : range endpoint = sourceMap '' S.space
  nonneg_preserved : ∀ (t : I) (x : Carrier),
    0 ≤ r (projection x) → 0 ≤ r (projection (deformation (t, x)))
  zero_preserved : ∀ (t : I) (x : Carrier),
    r (projection x) = 0 → r (projection (deformation (t, x))) = 0

attribute [instance] Stage.topology Stage.t2 Stage.locallyCompact Stage.pathConnected

variable {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}



def Stage.source (s : Stage e S f r C) : C(S.space, s.Carrier) :=
  ⟨fun x => s.sourceMap x, s.sourcePL.continuousOn.domRestrict⟩

theorem Stage.range_source (s : Stage e S f r C) :
    range s.source = s.sourceMap '' S.space :=
  range_domRestrict s.sourceMap S.space



theorem Stage.chart_source (s : Stage e S f r C) (k : s.Index) :
    MapsTo s.projection (s.charts k).source (e (s.chartIndex k)).source := by
  intro x hx
  have hz := (s.charts k).map_source hx
  have hi := s.chart_inverse k hz
  have he := (e (s.chartIndex k)).map_target (s.chart_target k hz)
  change s.projection ((s.charts k).symm (s.charts k x)) =
    (e (s.chartIndex k)).symm (s.charts k x) at hi
  rw [(s.charts k).left_inv hx] at hi
  exact hi.symm ▸ he



theorem Stage.cutPL (s : Stage e S f r C)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) :
    ∀ k, LocallyPiecewiseAffineOn
      ((r ∘ s.projection) ∘ (s.charts k).symm) (s.charts k).target := by
  intro k
  apply ((hrPL (s.chartIndex k)).mono (s.charts k).open_target
    (s.chart_target k)).congr
  intro y hy
  exact congrArg r (s.chart_inverse k hy).symm




theorem Stage.graph_local (s : Stage e S f r C) {G : Type*}
    (q : M → G) (hq : InjOn q C) : IsLocallyInjective (q ∘ s.projection) := by
  intro x
  obtain ⟨V, hV, hx, hinj⟩ := s.projectionLocal.isLocallyInjective x
  refine ⟨V, hV, hx, ?_⟩
  intro y hy z hz he
  exact hinj hy hz (hq (s.projection_mem y) (s.projection_mem z) he)



theorem Stage.frontier_region (s : Stage e S f r C) (R : Set M) :
    frontier (s.projection ⁻¹' R) = s.projection ⁻¹' frontier R :=
  (s.projectionLocal.isOpenMap.preimage_frontier_eq_frontier_preimage
    s.projection.continuous R).symm



theorem Stage.halfspace_boundary (s : Stage e S f r C) {R : Set M}
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∀ x ∈ frontier (s.projection ⁻¹' R),
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph s.Carrier E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y) :=
  s.projectionLocal.halfspace_boundary_preimage e s.charts s.chartIndex
    s.chart_target s.chart_inverse hboundary




theorem exists_initial_stage [T2Space M] [LocallyCompactSpace M]
    [FiniteDimensional ℝ U] [PathConnectedSpace S.space]
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hS : S.faces.Finite) (hf : PolyhedralPLInCharts e f S.space)
    (v0 : S.space) (hAC : f '' S.space ⊆ interior C)
    (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) :
    ∃ s : Stage e S f r C, IsOpenEmbedding s.projection := by
  obtain ⟨z, _, _, _, _, _, _, _, hlevel⟩ :=
    OpenPartialHomeomorph.exists_polyhedral_image_open_cut_deformation e hcompat hcover
      S hS hf isOpen_interior (fun x hx => hAC (mem_image_of_mem f hx)) hr hrPL
  obtain ⟨_, hO, hAO, hOP, hPC, a, H, ha, hpos, hzero, _⟩ :=
    hlevel (1 / 2) (by norm_num) (by norm_num)
  let O : Set M := {x | (1 : ℝ) / 2 < z x}
  have hA : IsPathConnected (f '' S.space) := by
    simpa only [range_domRestrict] using isPathConnected_range hf.continuousOn.domRestrict
  have hpath : PathConnectedSpace O := by
    apply H.toHomotopy.pathConnectedSpace_of_range
    rw [ha]
    exact hA.preimage_coe hAO
  let : LocallyCompactSpace O := hO.locallyCompactSpace
  let : PathConnectedSpace O := hpath
  obtain ⟨d, g, hdcover, hdcompat, hdtarget, hdval, hdinv, hg, hgf, himage⟩ :=
    hf.exists_open_restriction hcover hcompat S hS v0 hO
      (fun x hx => hAO (mem_image_of_mem f hx))
  let j : C(O, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let H' : (ContinuousMap.id O).HomotopyRel a (g '' S.space) :=
    { H.toHomotopy with prop' := fun t _ hx => H.eq_fst t (himage.subset hx) }
  let s : Stage e S f r C :=
    { Carrier := O
      Index := ι × O
      charts := d
      cover := hdcover
      compatible := hdcompat
      projection := j
      projectionLocal := hO.isOpenEmbedding_subtypeVal.isLocalHomeomorph
      projection_mem := fun x => interior_subset (hPC (hOP x.property))
      chartIndex := Prod.fst
      chart_target := hdtarget
      chart_forward := hdval
      chart_inverse := hdinv
      sourceMap := g
      sourcePL := hg
      source_eq := fun _ hx => hgf hx
      endpoint := a
      deformation := H'
      endpoint_range := ha.trans himage.symm
      nonneg_preserved := hpos
      zero_preserved := hzero }
  exact ⟨s, hO.isOpenEmbedding_subtypeVal⟩

end Geometry.OriginalPLTower
