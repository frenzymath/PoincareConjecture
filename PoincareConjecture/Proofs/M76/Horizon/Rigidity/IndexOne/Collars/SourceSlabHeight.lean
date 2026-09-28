import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.OldBoundaryStrips
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.RealLiftPL

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

noncomputable def sourceSlabHeight (phi : C(H, H)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < p) : C(sourceSlab phi a b, ℝ) where
  toFun z := (closedPhaseIntervalCoordinates a b ha hb).symm
    ⟨sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
      ⟨z.val, sourceSlab_subset phi a b z.property⟩),
      (mem_sourceSlab_iff phi a b _).mp z.property⟩
  continuous_toFun := by
    apply continuous_subtype_val.comp
    apply (closedPhaseIntervalCoordinates a b ha hb).symm.continuous.comp
    apply Continuous.subtype_mk
    exact (sourcePhase phi).continuous.comp
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous.comp
        (continuous_subtype_val.subtype_mk _))

theorem sourceSlabHeight_mem (phi : C(H, H)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < p) (z : sourceSlab phi a b) :
    sourceSlabHeight phi a b ha hb z ∈ Icc a b :=
  ((closedPhaseIntervalCoordinates a b ha hb).symm _).property

theorem sourceSlabHeight_coe (phi : C(H, H)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < p) (z : sourceSlab phi a b) :
    (sourceSlabHeight phi a b ha hb z : C) =
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
        ⟨z.val, sourceSlab_subset phi a b z.property⟩) :=
  congrArg Subtype.val ((closedPhaseIntervalCoordinates a b ha hb).apply_symm_apply _)

theorem sourceSlabHeight_eq_iff (phi : C(H, H)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : b < p) (z : sourceSlab phi a b) {t : ℝ} (ht : t ∈ Icc a b) :
    sourceSlabHeight phi a b ha hb z = t ↔ (z : X) ∈ sourceSurface phi (t : C) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hz := sourceSlabHeight_mem phi a b ha hb z
  have hzI : sourceSlabHeight phi a b ha hb z ∈ Ico (0 : ℝ) (0 + p) := by
    constructor <;> linarith [hz.1, hz.2]
  have htI : t ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [ht.1, ht.2]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico hzI htI, sourceSlabHeight_coe]
  exact (mem_sourceSurface_iff phi (t : C)
    ⟨z.val, sourceSlab_subset phi a b z.property⟩).symm

theorem finitePiecewiseAffineOn_sourceSlabHeight
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : α → OpenPartialHomeomorph X V3) (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (a b : ℝ) (ha : 0 ≤ a) (hb : b < p)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → sourceSlab phi a b) (hg : ContinuousOn g K.space)
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space) :
    FinitePiecewiseAffineOn (fun z => sourceSlabHeight phi a b ha hb (g z)) K.space := by
  let f : E → R := fun z => ⟨g z, sourceSlab_subset phi a b (g z).property⟩
  apply finitePiecewiseAffineOn_sourcePhase_lift e d hd phi hphi K hK f hgPL
    (fun z => sourceSlabHeight phi a b ha hb (g z))
    ((sourceSlabHeight phi a b ha hb).continuous.comp_continuousOn hg)
  exact fun z _ => sourceSlabHeight_coe phi a b ha hb (g z)

end PoincareConjecture.M76.HamiltonIntervalTorus
