import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.Affine
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Target.AffineQuotient
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.LinearTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "V0" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "pi" => latticeCoordinateProjection (Fin 0) (Fin 3) L0


noncomputable def hamiltonZeroTargetAffine (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c : C0 × C0) : C(X0, X0) :=
  ⟨fun y => (Q0).symm (affineIntegerMatrixMap (4 * (16 : ℝ)) A c (Q0 y).1, (Q0 y).2),
    (Q0).symm.continuous.comp
      (((affineIntegerMatrixMap (4 * (16 : ℝ)) A c).continuous.comp
        (Q0).continuous.fst).prodMk (Q0).continuous.snd)⟩

@[simp] theorem hamiltonZeroTargetAffine_apply (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c : C0 × C0) (y : X0) :
    hamiltonZeroTargetAffine A c y =
      (Q0).symm (affineIntegerMatrixMap (4 * (16 : ℝ)) A c (Q0 y).1, (Q0 y).2) := rfl

theorem hamiltonZeroTargetAffine_coordinates (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c : C0 × C0) (y : X0) :
    Q0 (hamiltonZeroTargetAffine A c y) =
      (affineIntegerMatrixMap (4 * (16 : ℝ)) A c (Q0 y).1, (Q0 y).2) :=
  (Q0).apply_symm_apply _

@[simp] theorem hamiltonZeroTargetAffine_phase (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c z : C0 × C0) (theta : C0) :
    hamiltonZeroTargetAffine A c ((Q0).symm (z, theta)) =
      (Q0).symm (affineIntegerMatrixMap (4 * (16 : ℝ)) A c z, theta) := by
  simp only [hamiltonZeroTargetAffine_apply, Homeomorph.apply_symm_apply]

theorem hamiltonZeroTargetAffine_normal (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c : C0 × C0) (y : X0) : (Q0 (hamiltonZeroTargetAffine A c y)).2 = (Q0 y).2 := by
  rw [hamiltonZeroTargetAffine_coordinates]

theorem hamiltonZeroTargetAffine_mk (A : Matrix (Fin 2) (Fin 2) ℤ)
    (s t : ℝ) (x : Fin 0 → ℝ) (v : V3) :
    hamiltonZeroTargetAffine A ((s : C0), (t : C0)) (x, QuotientAddGroup.mk v) =
      (x, QuotientAddGroup.mk
        ![s + (A 0 0 : ℝ) * v 0 + (A 0 1 : ℝ) * v 1,
          t + (A 1 0 : ℝ) * v 0 + (A 1 1 : ℝ) * v 1, v 2]) := by
  apply (Q0).injective
  rw [hamiltonZeroTargetAffine_coordinates]
  change (affineIntegerMatrixMap (4 * (16 : ℝ)) A ((s : C0), (t : C0))
    ((v 0 : C0), (v 1 : C0)), (v 2 : C0)) =
      (((((s + (A 0 0 : ℝ) * v 0 + (A 0 1 : ℝ) * v 1) : ℝ) : C0),
        ((((t + (A 1 0 : ℝ) * v 0 + (A 1 1 : ℝ) * v 1) : ℝ) : C0))), (v 2 : C0))
  simp [affineIntegerMatrixMap_apply, integerMatrixMap_apply, ← zsmul_eq_mul, add_assoc]


private def targetAffineLift (A : Matrix (Fin 2) (Fin 2) ℤ) (s t : ℝ) : V0 →ᴬ[ℝ] V0 :=
  let P (i : Fin 3) : V0 →L[ℝ] ℝ := ContinuousLinearMap.proj (Sum.inr i)
  let B : V0 →L[ℝ] V0 := ContinuousLinearMap.pi fun j =>
    match j with
    | Sum.inl i => Fin.elim0 i
    | Sum.inr i => ![(A 0 0 : ℝ) • P 0 + (A 0 1 : ℝ) • P 1,
        (A 1 0 : ℝ) • P 0 + (A 1 1 : ℝ) • P 1, P 2] i
  let c : V0 := fun j => match j with
    | Sum.inl i => Fin.elim0 i
    | Sum.inr i => ![s, t, 0] i
  ContinuousAffineMap.const ℝ V0 c + B.toContinuousAffineMap

private theorem targetAffineLift_projection (A : Matrix (Fin 2) (Fin 2) ℤ)
    (s t : ℝ) (v : V0) :
    hamiltonZeroTargetAffine A ((s : C0), (t : C0)) (pi v) =
      pi (targetAffineLift A s t v) := by
  change hamiltonZeroTargetAffine A ((s : C0), (t : C0))
    ((fun i => v (Sum.inl i)), QuotientAddGroup.mk (fun j => v (Sum.inr j))) = _
  rw [hamiltonZeroTargetAffine_mk]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply congrArg QuotientAddGroup.mk
    funext j
    fin_cases j <;> simp [targetAffineLift, add_assoc]

end PoincareConjecture.M76.LinearTorus

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))


theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetAffine
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (c : C0 × C0)
    {Y : E → X0} {S : Set E} (hY : PolyhedralPLInCharts d Y S) :
    PolyhedralPLInCharts d (LinearTorus.hamiltonZeroTargetAffine A c ∘ Y) S := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective c.1
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective c.2
  have hc : c = ((s : C0), (t : C0)) := Prod.ext hs.symm ht.symm
  rw [hc]
  exact hd.polyhedralPL_postcomp_quotient_affine _ (LinearTorus.targetAffineLift A s t)
    (LinearTorus.targetAffineLift_projection A s t) hY

end PoincareConjecture.M76
