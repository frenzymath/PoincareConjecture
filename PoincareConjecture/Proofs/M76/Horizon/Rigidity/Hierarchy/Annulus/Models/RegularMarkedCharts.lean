import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateSurface

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem HamiltonZeroSecondCoordinateRegularity.exists_marked_surface_chart
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi : C(H0, H0)} {theta : C0}
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    (x : X0) (hx : x ∈ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) :
    let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}
    ∃ T : OpenPartialHomeomorph X0 V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source (frontier R)) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) := by
  classical
  let S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}
  let x' : R := ⟨x, hx.1⟩
  by_cases hxB : x ∈ frontier R
  · obtain ⟨a, psi, ell, u, v, T, _, hu, hv, huv, hxT, _, _, hcompat,
      hregion, hmark, _, hlevel⟩ := hreg.2 x' hxB hx.2
    refine ⟨T, hxT, hcompat, Or.inr ⟨ell, psi, u, v, hu, hv, huv, ?_, hmark⟩⟩
    intro y hy
    constructor
    · intro hyS
      exact ⟨(hlevel ⟨y, hyS.1⟩ hy).mp hyS.2, (hregion y hy).mp hyS.1⟩
    · rintro ⟨hz, hpos⟩
      have hyR := (hregion y hy).mpr hpos
      exact ⟨hyR, (hlevel ⟨y, hyR⟩ hy).mpr hz⟩
  · obtain ⟨a, ell, v, T, _, hv, hxT, _, hcompat, _, hlevel⟩ := hreg.1 x' hx.2
    let B := T.restrOpen (interior R) isOpen_interior
    have hxint : x ∈ interior R := (mem_interior_iff_notMem_frontier hx.1).mpr hxB
    refine ⟨B, ⟨hxT, hxint⟩, ?_, Or.inl ⟨ell, v, hv, ?_, ?_⟩⟩
    · intro i
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcompat i)).mono
        ((e i).symm.trans B).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
    · intro y hy
      have hyR := interior_subset hy.2
      exact ⟨fun hyS => (hlevel ⟨y, hyR⟩ hy.1).mp hyS.2,
        fun hz => ⟨hyR, (hlevel ⟨y, hyR⟩ hy.1).mpr hz⟩⟩
    · exact disjoint_interior_frontier.mono_left (fun _ hy => hy.2)

end PoincareConjecture.M76
