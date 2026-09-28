import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerHandleCorrection
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "pi" => latticeCoordinateProjection ι κ L

private def latticeProjectionHom : V →+ LatticeHandleAmbient ι κ L where
  toFun := pi
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fintype ι] [Fintype κ] in
private theorem continuous_latticeProjection : Continuous pi := by
  exact (continuous_pi fun i => continuous_apply (Sum.inl i)).prodMk
    (QuotientAddGroup.continuous_mk.comp
      (continuous_pi fun i => continuous_apply (Sum.inr i)))

variable {ι κ L} {β : Type*}

omit [Fintype κ] in
private theorem StandardLatticeHandleAtlas.exists_projection_affine_chart
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d) (x : V) :
    ∃ (i : β) (a : V ≃ᴬ[ℝ] (Fin 3 → ℝ)) (U : Set V),
      IsOpen U ∧ x ∈ U ∧ MapsTo pi U (d i).source ∧
      EqOn ((d i) ∘ pi) a U := by
  obtain ⟨i, hi⟩ := hd.domain.cover (pi x)
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ
    (fun _ => ℝ)).toContinuousAffineEquiv
  let a := a0.trans c.symm
  have ha (z : Fin 3 → ℝ) (hz : z ∈ (d i).target) : pi (a z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let z0 := d i (pi x)
  have hz0 : z0 ∈ (d i).target := (d i).mapsTo hi
  have hcenter : pi (a z0) = pi x := (ha z0 hz0).trans ((d i).left_inv hi)
  let b := a.trans (ContinuousAffineEquiv.constVAdd ℝ V (x - a z0))
  have hb (z : Fin 3 → ℝ) (hz : z ∈ (d i).target) : pi (b z) = (d i).symm z := by
    change latticeProjectionHom ι κ L ((x - a z0) + a z) = (d i).symm z
    rw [map_add, map_sub]
    change pi x - pi (a z0) + pi (a z) = (d i).symm z
    rw [hcenter, sub_self, zero_add, ha z hz]
  refine ⟨i, b.symm, b '' (d i).target,
    b.toHomeomorph.isOpenMap _ (d i).open_target, ?_, ?_, ?_⟩
  · refine ⟨z0, hz0, ?_⟩
    change (x - a z0) + a z0 = x
    abel
  · rintro _ ⟨z, hz, rfl⟩
    rw [hb z hz]
    exact (d i).mapsTo_symm hz
  · rintro _ ⟨z, hz, rfl⟩
    change d i (pi (b z)) = b.symm (b z)
    rw [hb z hz, (d i).right_inv hz, b.symm_apply_apply]

theorem StandardLatticeHandleAtlas.polyhedralPL_projection
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d)
    {v : W → V} {S : Set W} (hv : FinitePiecewiseAffineOn v S) :
    PolyhedralPLInCharts d (pi ∘ v) S := by
  obtain ⟨K, hK, rfl, hvK⟩ := hv
  have hv := hvK.finitePiecewiseAffineOn hK
  refine ⟨(continuous_latticeProjection ι κ L).comp_continuousOn hv.continuousOn, ?_⟩
  intro x
  obtain ⟨i, a, U, hU, hxU, hUs, hcoords⟩ := hd.exists_projection_affine_chart (v x)
  let O : Set K.space := (fun y : K.space => v y) ⁻¹' U
  have hO : IsOpen O := hU.preimage
    (hv.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property))
  obtain ⟨N, W0, hN, hNK, hW0, hxW0, hWN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxU
  have hNU (y : W) (hy : y ∈ N.space) : v y ∈ U :=
    hNO (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
  refine ⟨i, N, W0, hN, hNK, hW0, hxW0, hWN, ?_, ?_⟩
  · intro y hy
    exact hUs (hNU y hy)
  · apply ((hv.restrict N hN hNK).postcomp a.toContinuousAffineMap).congr
    intro y hy
    exact (hcoords (hNU y hy)).symm

theorem StandardLatticeHandleAtlas.polyhedralPL_inverse_compression
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (p : OpenPartialHomeomorph V V)
    (hp : LocallyPiecewiseAffineOn p.symm p.target)
    (Q : V ≃ₜ V) (hQ : FinitePiecewiseAffineOn Q (closedBall (0 : V) 1))
    (hQt : MapsTo Q (closedBall (0 : V) 1) p.target) :
    PolyhedralPLInCharts d (pi ∘ p.symm ∘ Q) (closedBall (0 : V) 1) := by
  exact hd.polyhedralPL_projection (hp.comp_finitePiecewiseAffineOn hQ hQt)

end PoincareConjecture.M76
