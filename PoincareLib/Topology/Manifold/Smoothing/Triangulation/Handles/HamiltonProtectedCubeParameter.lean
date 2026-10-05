import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Coverings.HamiltonProtectedParameterLift
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall

/-!
# Whole protected cube parameters in the actual comparison image

The fixed unit cube has a finite triangulation. Its original quotient
parameter is therefore an input to the same-lift PL theorem, without
an additional finite-source supplier. See Hamilton 1976, pp.67--68 and
M76 derivation347.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {α β γ : Type*}

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "R" => latticeHandleDomain ι κ L
local notation "X" => LatticeHandleAmbient ι κ L

/-- The actual whole cube parameter acquires a finite PL A-image from
its original quotient map and the same protected comparison. This is
used for both the enclosing three-ball and each marked two-disk.
See Hamilton pp.67--68 and derivation347. -/
theorem protected_cube_image_isFinitePL
    (e : α → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (e' : γ → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (N : Set X)
    (hidentity : ChartwisePLOn e e' (ContinuousMap.id R)
      ((Subtype.val : R → X) ⁻¹' N))
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L)
    (hg : ChartwisePLHomeomorph e' d (latticeHandleHomeomorphInDomain ι κ L g))
    (G : D ≃ₜ D)
    (hG : ∀ y, ((coordinateCylinderProduct ι κ (G y)).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G y)).2) =
      g ((coordinateCylinderProduct ι κ y).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ y).2))
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hp : LocallyPiecewiseAffineOn p p.source)
    (A : V ≃ₜ V) (hA : ∀ y : D, A (p y) = p (G y))
    (P : Set V) (hPD : P ⊆ D) (hPfix : EqOn p id P)
    (hPN : ∀ y ∈ P, latticeCoordinateProjection ι κ L y ∈ N)
    {n : ℕ} (u : closedBall (0 : Fin n → ℝ) 1 ≃ₜ P)
    (f : (Fin n → ℝ) → X)
    (hf : PolyhedralPLInCharts e f (closedBall (0 : Fin n → ℝ) 1))
    (hfu : ∀ x : closedBall (0 : Fin n → ℝ) 1,
      f x = latticeCoordinateProjection ι κ L (u x)) :
    (u.trans (A.image P)).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin n)
  let uK : K.space ≃ₜ P := (Homeomorph.setCongr hKC).trans u
  have hfK : PolyhedralPLInCharts e f K.space := by rw [hKC]; exact hf
  have hfuK (x : K.space) : f x = latticeCoordinateProjection ι κ L (uK x) :=
    hfu (Homeomorph.setCongr hKC x)
  obtain ⟨fA, hfA, hval⟩ := protected_image_isFinitePL_of_quotient_parameterization
    e e' d hd N hidentity g hg G hG p hps hp A hA P hPD hPfix hPN K hK uK f hfK hfuK
  refine ⟨fA, ?_, ?_⟩
  · rwa [hKC] at hfA
  · intro x
    exact hval ⟨x, hKC.symm ▸ x.property⟩

end PoincareMT.M76
