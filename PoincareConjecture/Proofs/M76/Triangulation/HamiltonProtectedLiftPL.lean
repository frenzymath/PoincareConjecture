import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerHandleCorrection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardLiftPL

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
local notation "W" => LatticeHandleAmbient ι κ L

theorem finitePL_compactified_protected_parameterization
    (e : α → OpenPartialHomeomorph W (Fin 3 → ℝ))
    (e' : γ → OpenPartialHomeomorph W (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph W (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (N : Set R) (hidentity : ChartwisePLOn e e' (ContinuousMap.id R) N)
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L)
    (hg : ChartwisePLHomeomorph e' d (latticeHandleHomeomorphInDomain ι κ L g))
    (G : D ≃ₜ D)
    (hG : ∀ y, ((coordinateCylinderProduct ι κ (G y)).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G y)).2) =
      g ((coordinateCylinderProduct ι κ y).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ y).2))
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hp : LocallyPiecewiseAffineOn p p.source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (param : E → D) (hparam : ContinuousOn param K.space)
    (hparamPL : PolyhedralPLInCharts e
      (fun x => (cylinderLatticeProjection ι κ L (param x) : W)) K.space)
    (hparamN : MapsTo (fun x => cylinderLatticeProjection ι κ L (param x)) K.space N) :
    FinitePiecewiseAffineOn (fun x => p (G (param x))) K.space := by
  let q : E → R := fun x => cylinderLatticeProjection ι κ L (param x)
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hparamPL.continuousOn
  have hprime : PolyhedralPLInCharts e' (fun x => (q x : W)) K.space :=
    hidentity.polyhedralPLInCharts_comp K hK q hq hparamPL hparamN
  let r := latticeHandleHomeomorphInDomain ι κ L g
  have hstandard : PolyhedralPLInCharts d (fun x => (r (q x) : W)) K.space :=
    hg.1.polyhedralPLInCharts_comp K hK q hq hprime (mapsTo_univ _ _)
  have hquot (y : D) : r (cylinderLatticeProjection ι κ L y) =
      cylinderLatticeProjection ι κ L (G y) := by
    apply (latticeHandleDomainEquiv ι κ L).injective
    exact (hG y).symm
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ
    (fun _ => ℝ)).toContinuousAffineEquiv
  have hcont : ContinuousOn (fun x => c (G (param x))) K.space :=
    (c.continuous.comp (continuous_subtype_val.comp G.continuous)).comp_continuousOn hparam
  have hproduct : FinitePiecewiseAffineOn (fun x => c (G (param x))) K.space := by
    apply hd.finitePiecewiseAffineOn_lift K hK (fun x => (r (q x) : W))
      hstandard (fun x => c (G (param x))) hcont
    intro x _
    rw [show r (q x) = cylinderLatticeProjection ι κ L (G (param x)) from hquot (param x)]
    rfl
  have hlift : FinitePiecewiseAffineOn (fun x => (G (param x) : V)) K.space :=
    (hproduct.postcomp c.symm.toContinuousAffineMap).congr (by
      intro x _
      exact c.symm_apply_apply (G (param x)))
  exact hp.comp_finitePiecewiseAffineOn hlift (by
    intro x _
    rw [hps]
    exact mem_univ _)

end PoincareConjecture.M76
