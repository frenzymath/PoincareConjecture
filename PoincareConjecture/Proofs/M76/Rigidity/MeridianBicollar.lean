import PoincareConjecture.Proofs.M76.Rigidity.StandardMeridian
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerPeriodLattice
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩

noncomputable def hamiltonSolidTorusCircleEquiv : T ≃ₜ AddCircle p :=
  (hamiltonLowerLatticePiEquiv (Fin 1)).trans
    (Homeomorph.funUnique (Fin 1) (AddCircle p))

theorem hamiltonSolidTorusCircleEquiv_mk (t : ℝ) :
    hamiltonSolidTorusCircleEquiv (QuotientAddGroup.mk (fun _ : Fin 1 => t)) =
      (t : AddCircle p) := rfl

theorem hamiltonSolidTorusCircleEquiv_symm_coe (t : ℝ) :
    hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p) =
      QuotientAddGroup.mk (fun _ : Fin 1 => t) := by
  apply hamiltonSolidTorusCircleEquiv.injective
  rw [hamiltonSolidTorusCircleEquiv.apply_symm_apply,
    hamiltonSolidTorusCircleEquiv_mk]

noncomputable def hamiltonMeridianBicollar : OpenPartialHomeomorph (D × ℝ) H :=
  (OpenPartialHomeomorph.refl D).prod
    ((AddCircle.shortArcQuotient p 1).trans
      hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph)

theorem hamiltonMeridianBicollar_source :
    hamiltonMeridianBicollar.source = univ ×ˢ Ioo (-1) 1 := by
  change univ ×ˢ ((AddCircle.shortArcQuotient p 1).trans
    hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph).source = _
  rw [OpenPartialHomeomorph.trans_source]
  change univ ×ˢ ((AddCircle.shortArcQuotient p 1).source ∩
    (AddCircle.shortArcQuotient p 1) ⁻¹' univ) = _
  rw [preimage_univ, inter_univ,
    AddCircle.shortArcQuotient_source p (by norm_num)]

theorem hamiltonMeridianBicollar_target :
    hamiltonMeridianBicollar.target =
      {z : H | hamiltonSolidTorusCircleEquiv z.2 ∈
        ((↑) : ℝ → AddCircle p) '' Ioo (-1) 1} := by
  ext z
  change (True ∧ (True ∧ hamiltonSolidTorusCircleEquiv z.2 ∈
    (AddCircle.shortArcQuotient p 1).target)) ↔ _
  rw [AddCircle.shortArcQuotient_target p (by norm_num)]
  simp

theorem hamiltonMeridianBicollar_apply (x : D) (t : ℝ) :
    hamiltonMeridianBicollar (x, t) =
      (x, QuotientAddGroup.mk (fun _ : Fin 1 => t)) := by
  change (x, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) = _
  rw [hamiltonSolidTorusCircleEquiv_symm_coe]

theorem hamiltonMeridianBicollar_zero (x : D) :
    hamiltonMeridianBicollar (x, 0) = hamiltonStandardMeridian L x := by
  rw [hamiltonMeridianBicollar_apply]
  rfl

theorem hamiltonMeridianBicollar_mem_boundary (x : D) (t : ℝ) :
    hamiltonMeridianBicollar (x, t) ∈ latticeHandleBoundary (Fin 2) (Fin 1) L ↔
      ‖(x : V2)‖ = 1 := by
  rw [hamiltonMeridianBicollar_apply]
  change (‖(x : V2)‖ = 1 ∧ True) ↔ ‖(x : V2)‖ = 1
  exact ⟨And.left, fun hx => ⟨hx, trivial⟩⟩

theorem hamiltonMeridianBicollar_ambient_apply (x : D) (t : ℝ) :
    (((hamiltonMeridianBicollar (x, t)).1 : V2),
      (hamiltonMeridianBicollar (x, t)).2) =
        latticeCoordinateProjection (Fin 2) (Fin 1) L
          (Sum.elim (x : V2) (fun _ : Fin 1 => t)) := by
  rw [hamiltonMeridianBicollar_apply]
  rfl

theorem StandardLatticeHandleAtlas.polyhedralPL_meridianBox
    {β : Type*}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d (latticeCoordinateProjection (Fin 2) (Fin 1) L)
      (closedBall (0 : (Fin 2 ⊕ Fin 1) → ℝ) 1) := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ :=
    (Set.isFinitePLBallPair_unit_cube (ι := Fin 2 ⊕ Fin 1))
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := he
  have hi : FinitePiecewiseAffineOn (id : ((Fin 2 ⊕ Fin 1) → ℝ) → _)
      (closedBall (0 : (Fin 2 ⊕ Fin 1) → ℝ) 1) :=
    ⟨K, hK, hKD, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ _)⟩
  exact hd.polyhedralPL_projection hi

end PoincareConjecture.M76
