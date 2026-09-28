import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedImageParameters
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {E α β γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "R" => latticeHandleDomain ι κ L
local notation "X" => LatticeHandleAmbient ι κ L

theorem protected_image_isFinitePL_of_quotient_parameterization
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
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (u : K.space ≃ₜ P) (f : E → X)
    (hf : PolyhedralPLInCharts e f K.space)
    (hfu : ∀ x : K.space, f x = latticeCoordinateProjection ι κ L (u x)) :
    (u.trans (A.image P)).IsFinitePL := by
  classical
  let uD : K.space → D := fun x => ⟨u x, hPD (u x).property⟩
  let z : D := ⟨0, by intro j _; simp⟩
  let param : E → D := fun x => if hx : x ∈ K.space then uD ⟨x, hx⟩ else z
  have hparamval (x : K.space) : (param x : V) = (u x : V) := by
    simp only [param, dif_pos x.property, uD]
  have hparam : ContinuousOn param K.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : K.space.domRestrict param = uD := by
      funext x
      change param x = uD x
      simp only [param, dif_pos x.property]
    rw [heq]
    exact (continuous_subtype_val.comp u.continuous).subtype_mk _
  have hfparam : PolyhedralPLInCharts e
      (fun x => (cylinderLatticeProjection ι κ L (param x) : X)) K.space := by
    apply hf.congr
    intro x hx
    change f x = latticeCoordinateProjection ι κ L (param x)
    rw [hparamval ⟨x, hx⟩]
    exact hfu ⟨x, hx⟩
  have hparamN : MapsTo (fun x => cylinderLatticeProjection ι κ L (param x))
      K.space ((Subtype.val : R → X) ⁻¹' N) := by
    intro x hx
    change latticeCoordinateProjection ι κ L (param x) ∈ N
    rw [hparamval ⟨x, hx⟩]
    exact hPN (u ⟨x, hx⟩) (u ⟨x, hx⟩).property
  have hPL := finitePL_compactified_protected_parameterization e e' d hd
    ((Subtype.val : R → X) ⁻¹' N) hidentity g hg G hG p hps hp
    K hK param hparam hfparam hparamN
  exact compactified_protected_image_isFinitePL u param hparamval p hPfix G A hA hPL

end PoincareConjecture.M76
