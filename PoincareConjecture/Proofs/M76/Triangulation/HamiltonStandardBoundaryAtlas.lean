import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardAtlasExistence
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinderHalfspace
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)

omit [Fintype κ] in

theorem standardLatticeHandleAtlas_of_affine_cover
    [Finite κ]
    {α : Type*}
    (d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (hcover : ∀ x, ∃ j, x ∈ (d j).source)
    (hcompat : ∀ i j, (d i).symm.trans (d j) ∈ piecewiseAffineGroupoid V3)
    (hformula : ∀ j, ∃ a : V3 ≃ᴬ[ℝ] ((ι → ℝ) × (κ → ℝ)),
      ∀ z ∈ (d j).target, (d j).symm z = ((a z).1, QuotientAddGroup.mk (a z).2)) :
    StandardLatticeHandleAtlas ι κ L d := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  refine ⟨⟨hcover, hcompat, isClosed_closedBall.prod isClosed_univ, ?_⟩, hformula⟩
  intro x hx
  obtain ⟨j, hjx⟩ := hcover x
  obtain ⟨a, ha⟩ := hformula j
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ
    (fun _ => ℝ)).toContinuousAffineEquiv
  let A : V3 ≃ᴬ[ℝ] V := a.trans c.symm
  let q := (d j).transHomeomorph A.toHomeomorph
  have hqcoord (y : LatticeHandleAmbient ι κ L) (hy : y ∈ q.source) :
      (fun i : ι => q y (Sum.inl i)) = y.1 := by
    change (a (d j y)).1 = y.1
    exact congrArg Prod.fst ((ha _ ((d j).mapsTo hy)).symm.trans ((d j).left_inv hy))
  have himage : q.IsImage (latticeHandleDomain ι κ L) (coordinateCylinder J) := by
    intro y hy
    constructor
    · intro hyD
      refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      have h := hyD (Sum.inl i) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      have hcoord := congrFun (hqcoord y hy) i
      simpa only [hcoord, Real.norm_eq_abs] using h
    · intro hyR t ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht
      have hnorm := mem_closedBall_zero_iff.mp hyR.1
      have hi := (norm_le_pi_norm y.1 i).trans hnorm
      have hcoord := congrFun (hqcoord y hy) i
      change |q y (Sum.inl i)| ≤ 1
      rw [hcoord]
      simpa only [Real.norm_eq_abs] using hi
  have hqx : q x ∈ frontier (coordinateCylinder J) :=
    (himage.frontier.apply_mem_iff hjx).mpr hx
  obtain ⟨ell, w, H, hw, hxH, hHx, hzero, hHPL, hhalf⟩ :=
    exists_coordinateCylinder_halfspace_chart J hqx
  let T : OpenPartialHomeomorph V3 V3 :=
    (A.toHomeomorph.transOpenPartialHomeomorph H).transHomeomorph A.symm.toHomeomorph
  have hTPL : T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hpre := hHPL.1.comp
      (locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ)
    have hpost := (locallyPiecewiseAffineOn_affine
      A.symm.toContinuousAffineMap isOpen_univ).comp hpre
    change LocallyPiecewiseAffineOn (fun z => A.symm (H (A z))) (A ⁻¹' H.source)
    simpa only [preimage_univ, inter_univ, univ_inter, Function.comp_def,
      ContinuousAffineEquiv.coe_toContinuousAffineMap] using hpost
  let B := (d j).trans T
  let ell' := ell.comp A.toContinuousAffineMap
  have hell (y : LatticeHandleAmbient ι κ L) : ell' (B y) = ell (H (q y)) := by
    change ell (A (A.symm (H (A (d j y))))) = ell (H (A (d j y)))
    rw [A.apply_symm_apply]
  refine ⟨ell', A.linear.symm w, B, ?_, ⟨hjx, hxH⟩, ?_, ?_, ?_⟩
  · change ell.contLinear (A.linear (A.linear.symm w)) = 1
    rw [A.linear.apply_symm_apply, hw]
  · rw [hell, hHx, hzero]
  · intro i
    change (d i).symm.trans ((d j).trans T) ∈ piecewiseAffineGroupoid V3
    rw [← OpenPartialHomeomorph.trans_assoc]
    exact (piecewiseAffineGroupoid V3).trans (hcompat i j) hTPL
  · intro y hy
    rw [hell]
    exact (himage.apply_mem_iff hy.1).symm.trans (hhalf (q y) hy.2)

theorem exists_standard_lattice_handle_atlas [DiscreteTopology L]
    (hdim : Fintype.card ι + Fintype.card κ = 3) :
    ∃ d : ((ι → ℝ) × (κ → ℝ)) →
        OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
      StandardLatticeHandleAtlas ι κ L d := by
  obtain ⟨d, hcover, hcompat, hformula⟩ :=
    exists_standard_lattice_coordinate_cover ι κ L hdim
  exact ⟨d, standardLatticeHandleAtlas_of_affine_cover ι κ L d hcover hcompat hformula⟩

end PoincareConjecture.M76
