import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.MotionImages
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.RepairPairs










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarSurfaceBranchMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : D.K.space} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarSurfaceBranchMotion step D.K D.endpoint R a b W ε)



theorem protected_contact_nonexceptional
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {v : V3} (hv : v ∈ N.fixed.space) (hvJ : v ∈ interior N.support.space)
    (hzero : (N.coordinates v).2 = 0) :
    ∃ x y : D.K.space, x ≠ y ∧
      D.endpoint x ∈ N.window.left.source ∧
      D.endpoint y ∈ N.window.right.source ∧
      D.projected x = N.chart.symm v ∧ D.projected y = N.chart.symm v ∧
      N.chart.symm v ∈ N.chart.source ∧ N.chart.symm v ∉ D.exceptionalValues := by
  have hvP : v ∈ N.source.space := (N.fixed_space.subset hv).1
  have hv0 : v ≠ 0 := by
    intro heq
    exact (N.fixed_space.subset hv).2 (heq.symm ▸ mem_ball_self N.radius_pos)
  let z := N.chart.symm v
  have hzQ : z ∈ N.chart.source := N.chart.map_target
    (N.support_target (interior_subset hvJ))
  have hQz : N.chart z = v := N.chart.right_inv
    (N.support_target (interior_subset hvJ))
  obtain ⟨⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩, _⟩ := N.source_space.subset hvP
  have hyr : (step.projection ∘ step.inclusion) xr = z := by
    have hxQ : N.window.right xr ∈ N.chart.source := hxr.2
    rw [congrFun N.window.right_eq xr] at hxQ
    apply N.chart.injOn hxQ hzQ
    change N.chart (N.window.right xr) = v at hrv
    rw [congrFun N.window.right_eq xr] at hrv
    exact hrv.trans hQz.symm
  have hl : z ∈ (step.projection ∘ step.inclusion) ''
      (D.endpoint '' D.K.space ∩ N.window.left.source) :=
    (N.left_plane z hzQ).mpr (by rw [hQz]; exact hzero)
  obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hl
  let x : D.K.space := ⟨ul, hul⟩
  let y : D.K.space := ⟨ur, hur⟩
  have hne : x ≠ y := by
    intro heq
    exact N.window.disjoint.ne_of_mem hxl hxr.1
      (hlu.symm.trans ((congrArg D.endpoint (congrArg Subtype.val heq)).trans hru))
  have hxz : D.projected x = z :=
    (congrArg (step.projection ∘ step.inclusion) hlu).trans hly
  have hyz : D.projected y = z :=
    (congrArg (step.projection ∘ step.inclusion) hru).trans hyr
  refine ⟨x, y, hne, hlu.symm ▸ hxl, hru.symm ▸ hxr.1, hxz, hyz, hzQ, ?_⟩
  intro he
  have hzE : z ∈ ((fun z : A × A => D.projected z.1) '' D.repairPairs) := by
    refine ⟨((x : A), (y : A)), ?_, hxz⟩
    exact (D.mem_repairPairs_iff x.property y.property
      (fun heq => hne (Subtype.ext heq)) (hxz.trans hyz.symm)).mpr (hxz.symm ▸ he)
  have hcenter : z = D.projected a := hW ⟨(N.chart_inside hzQ).1, hzE⟩
  exact hv0 (hQz.symm.trans ((congrArg N.chart hcenter).trans N.centered))



theorem exists_protected_target_crossing
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {v : V3} (hv : v ∈ N.fixed.space) (hvJ : v ∈ interior N.support.space)
    (hzero : (N.coordinates v).2 = 0) :
    ∃ (x y : D.K.space) (left right : OpenPartialHomeomorph t.Carrier s.Carrier)
      (T : OpenPartialHomeomorph s.Carrier V3) (coord : V3 ≃L[ℝ] C3),
      D.endpoint x ∈ N.window.left.source ∧ D.endpoint y ∈ N.window.right.source ∧
      D.endpoint x ∈ left.source ∧ D.endpoint y ∈ right.source ∧
      D.projected x = N.chart.symm v ∧ D.projected y = N.chart.symm v ∧
      (left : t.Carrier → s.Carrier) = step.projection ∘ step.inclusion ∧
      (right : t.Carrier → s.Carrier) = step.projection ∘ step.inclusion ∧
      N.chart.symm v ∈ T.source ∧ T (N.chart.symm v) = 0 ∧
      (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ z ∈ T.source, z ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' D.K.space ∩ left.source) ↔ (coord (T z)).2 = 0) ∧
      ∀ z ∈ T.source, z ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' D.K.space ∩ right.source) ↔ (coord (T z)).1.1 = 0 := by
  obtain ⟨x, y, hne, hxl, hyr, hxz, hyz, hzQ, hex⟩ :=
    N.protected_contact_nonexceptional hW hv hvJ hzero
  obtain ⟨w, T, horder, hzT, _, hTzero, hTPL, _, _, hTl, hTr⟩ :=
    D.exists_whole_projected_crossing x.property y.property
      (fun he ↦ hne (Subtype.ext he)) (hxz.trans hyz.symm) (hxz.symm ▸ hex)
      N.chart.source N.chart.open_source (hxz.symm ▸ hzQ)
  have hzT' : N.chart.symm v ∈ T.source := hxz ▸ hzT
  have hTzero' : T (N.chart.symm v) = 0 := by simpa only [hxz] using hTzero
  rcases horder with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨x, y, w.left, w.right, T, crossingCoordinatesLeftLast.symm,
      hxl, hyr, hx, hy, hxz, hyz, w.left_eq, w.right_eq, hzT', hTzero', hTPL,
      hTl, hTr⟩
  · let perm : C3 ≃ₗ[ℝ] C3 :=
      { toFun := fun z ↦ ((z.2, z.1.2), z.1.1)
        invFun := fun z ↦ ((z.2, z.1.2), z.1.1)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact ⟨x, y, w.right, w.left, T,
      crossingCoordinatesLeftLast.symm.trans perm.toContinuousLinearEquiv,
      hxl, hyr, hx, hy, hxz, hyz, w.right_eq, w.left_eq, hzT', hTzero', hTPL,
      hTr, hTl⟩

end Geometry.OriginalPLTower.PlanarSurfaceBranchMotion

