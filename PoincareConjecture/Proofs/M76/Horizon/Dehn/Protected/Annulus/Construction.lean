import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Coordinates.RetainedShell
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)


theorem projected_sourceShell_protected
    (L : Submodule ℤ V2) {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    {x : V1 × V2} (hx : x ∈ sourceShell) :
    hamiltonMarkedProjection (Fin 1) (Fin 2) L x ∈
        hamiltonHandleBlock (Fin 1) (Fin 2) L 2 \
          hamiltonHandleBlock (Fin 1) (Fin 2) L 1 ∧
      hamiltonMarkedProjection (Fin 1) (Fin 2) L x ∈
        hamiltonMarkedProjection (Fin 1) (Fin 2) L ''
          (closedBall (0 : V1) 1 ×ˢ ball (0 : V2) 2) := by
  refine ⟨⟨⟨x, sourceShell_subset_block hx, rfl⟩, ?_⟩,
    ⟨x, ⟨hx.1, mem_ball_zero_iff.mpr hx.2.2⟩, rfl⟩⟩
  rintro ⟨y, hy, heq⟩
  have hy2 : y ∈ closedBall (0 : V1) 1 ×ˢ closedBall (0 : V2) 2 :=
    ⟨hy.1, closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hy.2⟩
  have hxy := retained.quotient_injective hy2 (sourceShell_subset_block hx) heq
  have hn : ‖x.2‖ ≤ 1 := mem_closedBall_zero_iff.mp (hxy ▸ hy.2)
  exact (not_lt_of_ge hn) hx.2.1



theorem exists_protected_annulus_of_chart
    (L : Submodule ℤ V2) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3)
    (he : PLDomain e (latticeHandleDomain (Fin 1) (Fin 2) L))
    (h : OpenPartialHomeomorph (V1 × V2) V3)
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    (k : (V1 × V2) → chartShell L retained)
    (hk : PolyhedralPLInCharts
      (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
        (chartShell_nonempty L retained)) k source)
    (hki : Topology.IsEmbedding (fun x : source ↦ k x))
    (hkin : MapsTo k source (chartDomain L retained))
    (hkb : ∀ x ∈ sphere (0 : V1) 1 ×ˢ sphere (0 : V2) 1,
      (k x : V3) = h (coordinates x))
    (hkfront : ∀ x : source, k x ∈ frontier (chartDomain L retained) ↔
      x.val.1 ∈ sphere (0 : V1) 1) :
    ∃ T : HamiltonProtectedDehnAnnulus L e,
      (∀ x, T.map x = (e retained.index).symm (k x : V3)) ∧
      IsCompact T.surface := by
  classical
  let f : (V1 × V2) → V3 := fun x ↦ k x
  obtain ⟨K, hK, hKs⟩ := exists_source_triangulation
  have hf : FinitePiecewiseAffineOn f source := by
    rw [← hKs]
    exact (hKs ▸ hk).finitePiecewiseAffineOn_fixed_chart
      (chartDomain_PL L retained he).compatible K hK () (fun _ _ ↦ mem_univ _)
  let A : Set V3 := range (fun x : source ↦ f x)
  have hfi : Topology.IsEmbedding (fun x : source ↦ f x) :=
    Topology.IsEmbedding.subtypeVal.comp hki
  let p : source ≃ₜ A := hfi.toHomeomorph
  have hAt : A ⊆ (e retained.index).target := by
    rintro z ⟨x, rfl⟩
    exact chartShell_subset_target L retained (k x).property
  let q := (e retained.index).symm.homeomorphOfImageSubsetSource hAt rfl
  let b := p.trans q
  let j := (e retained.index).symm ∘ f
  have hj : PolyhedralPLInCharts e j source := by
    rw [← hKs]
    exact polyhedralPLInCharts_of_one_chart_inverse K hK (hKs ▸ hf) retained.index
      (fun x _ ↦ chartShell_subset_target L retained (k x).property)
  have hprotected (y) (hy : y ∈ (e retained.index).symm '' A) :
      y ∈ hamiltonHandleBlock (Fin 1) (Fin 2) L 2 \
          hamiltonHandleBlock (Fin 1) (Fin 2) L 1 ∧
        y ∈ hamiltonMarkedProjection (Fin 1) (Fin 2) L ''
          (closedBall (0 : V1) 1 ×ˢ ball (0 : V2) 2) := by
    obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hy
    have hx : (k x : V3) ∈ shell h := by
      rw [← chartDomain_image L retained]
      exact ⟨k x, hkin x.property, rfl⟩
    obtain ⟨u, hu, hue⟩ := hx
    dsimp only [f]
    rw [← hue, chartShell_inverse_formula L retained hu]
    exact projected_sourceShell_protected L retained hu
  refine ⟨{
    surface := (e retained.index).symm '' A
    parametrization := b
    map := j
    map_eq := fun _ ↦ rfl
    piecewiseAffine := hj
    inside := fun y hy ↦ (hprotected y hy).1
    inside_outer_open := fun y hy ↦ (hprotected y hy).2
    boundary_values := ?_
    old_boundary_iff := ?_
  }, fun _ ↦ rfl, ?_⟩
  · intro x hx
    change (e retained.index).symm (k x : V3) = _
    rw [hkb x hx, chartShell_inverse_formula L retained
      (coordinates_mem_sourceShell ⟨sphere_subset_closedBall hx.1, hx.2⟩)]
    rfl
  · intro x
    change (e retained.index).symm (k x : V3) ∈
      frontier (latticeHandleDomain (Fin 1) (Fin 2) L) ↔ _
    rw [← hkfront x]
    rw [show frontier (chartDomain L retained) =
      {z : chartShell L retained | (e retained.index).symm (z : V3) ∈
        frontier (latticeHandleDomain (Fin 1) (Fin 2) L)} from
      frontier_chart_image_eq (e retained.index) (chartShell L retained)
        (chartShell_nonempty L retained) (chartShell_subset_target L retained) _]
    rfl
  · have : CompactSpace source :=
      isCompact_iff_compactSpace.mp
        ((isCompact_closedBall (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
    let : CompactSpace ((e retained.index).symm '' A) := b.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
