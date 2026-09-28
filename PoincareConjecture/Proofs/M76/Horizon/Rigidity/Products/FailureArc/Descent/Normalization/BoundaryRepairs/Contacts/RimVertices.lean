import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Cofaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.RepairPairs

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {K₀ A₀ : SimplicialComplex ℝ P2}
  {j : P2 → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.boundary_pair_mem_repairPairs
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    {x y : P2} (hx : x ∈ D.K.space) (hy : y ∈ D.K.space)
    (hne : x ≠ y) (hxy : D.projected x = D.projected y) (hxRim : x ∈ A₀.space) :
    (x, y) ∈ D.repairPairs := by
  apply (D.mem_repairPairs_iff hx hy hne hxy).mpr
  by_contra hn
  exact disjoint_left.mp disjoint_interior_frontier
    (D.double_point_interior_of_not_exceptional hx hy hne hxy hn)
    ((D.projected_proper x hx).mpr hxRim)

theorem MarkedSurfacePositionData.protected_annulus_boundary_vertices_nonzero
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
    (A : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
    (hseparate : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆
      {D.projected a}) :
    ∀ v ∈ A.fixedRim.vertices, (A.coordinates v).2 ≠ 0 := by
  intro v hv hvzero
  let p := step.projection ∘ step.inclusion
  have hvK := A.fixed_rim_space.subset (A.fixedRim.vertices_subset_space hv)
  have hvP := hvK.1
  have hvJ := (A.boundary_space.subset hvP).2
  have hv0 : v ≠ 0 := by
    intro heq
    rcases hvK.2 with hC | hfront
    · exact (A.fixed_space.subset hC).2 (heq.symm ▸ mem_ball_self A.radius_pos)
    · exact hfront.2 (heq.symm ▸ A.center_interior)
  let y := A.chart.symm v
  have hyQ : y ∈ A.chart.source := A.chart.map_target (A.support_target hvJ)
  have hQy : A.chart y = v := A.chart.right_inv (A.support_target hvJ)
  obtain ⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩ := (A.boundary_space.subset hvP).1
  have hyr : p xr = y := by
    have hxQ : p xr ∈ A.chart.source := by
      have h : A.window.right xr ∈ A.chart.source := hxr.2
      rw [congrFun A.window.right_eq xr] at h
      exact h
    apply A.chart.injOn hxQ hyQ
    change A.chart (A.window.right xr) = v at hrv
    rw [congrFun A.window.right_eq xr] at hrv
    exact hrv.trans hQy.symm
  have hyplane : y ∈ p '' (D.endpoint '' Ann ∩ A.window.left.source) :=
    (A.left_halfplane y hyQ).mpr ⟨by
        have hvh : (A.coordinates v).1.1 = 0 := (A.boundary_level.subset hvP).2
        rw [hQy]
        exact le_of_eq hvh.symm,
      by rw [hQy]; exact hvzero⟩
  obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hyplane
  have hurD : ur ∈ Ann := by
    apply mem_squareAnnulus_iff_depth.mpr
    rcases hur with h | h <;> rw [h] <;> norm_num
  have hne : ur ≠ ul := by
    intro heq
    have he : xr = xl := hru.symm.trans ((congrArg D.endpoint heq).trans hlu)
    exact A.window.disjoint.ne_of_mem hxl hxr.1 he.symm
  have hrvalue : D.projected ur = y := (congrArg p hru).trans hyr
  have hlvalue : D.projected ul = y := (congrArg p hlu).trans hly
  have hpair : (ur, ul) ∈ D.repairPairs := D.boundary_pair_mem_repairPairs
    (hAnn.symm.subset hurD) (hAnn.symm.subset hul) hne
    (hrvalue.trans hlvalue.symm) (hRim.symm.subset hur)
  have hybad : y ∈ (fun z : P2 × P2 => D.projected z.1) '' D.repairPairs :=
    ⟨(ur, ul), hpair, hrvalue⟩
  have hycenter : y = D.projected a := hseparate ⟨(A.chart_inside hyQ).1, hybad⟩
  exact hv0 (hQy.symm.trans ((congrArg A.chart hycenter).trans A.centered))

theorem MarkedSurfacePositionData.moved_annulus_boundary_vertices_nonzero
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
    (A : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
    (hseparate : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆
      {D.projected a})
    (K : SimplicialComplex ℝ V3)
    (hvertices : K.vertices = A.motion.map 1 '' A.rimComplex.vertices) :
    ∀ v ∈ K.vertices, (A.coordinates v).2 ≠ 0 := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hvertices.subset hv
  intro hz
  obtain ⟨hprotected, hzero⟩ := (A.zero_vertices u hu).mp hz
  exact D.protected_annulus_boundary_vertices_nonzero hAnn hRim A hseparate
    u hprotected hzero

end Geometry.OriginalPLTower
