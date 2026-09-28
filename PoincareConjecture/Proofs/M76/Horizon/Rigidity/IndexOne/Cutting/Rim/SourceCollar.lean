import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.PhaseInjection

set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem exists_sourcePhase_rim_collar
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (he : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) =
      (sourceSlab phi u v ∩ frontier R) ∪
        (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hdis : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ U : Set (sourceSurface phi theta), IsOpen U ∧
      ∃ c : (↥(sourceSurface phi theta ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ U,
        ∀ x, (c (collarBase x) : sourceSurface phi theta) =
          Set.inclusion inter_subset_left x := by
  let : TopologicalSpace.MetrizableSpace
      ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let N := sourceSlab phi u v
  let S0 := sourceSurface phi theta
  let S : Set (frontier N) := Subtype.val ⁻¹' S0
  let O : Set (frontier N) :=
    Subtype.val ⁻¹' ((N ∩ frontier R) ∪ sourceSurface phi theta')
  obtain ⟨hSF, hSc, hOc, hcover, hrim, hcompact, hne, hlocal⟩ :=
    sourcePhase_frontier_signed_data e phi F he hfront hdis hcorner
  obtain ⟨hboundary, _, A, hpos, _⟩ :=
    exists_side_collars_of_signed_rim_charts hSc hOc hcover hcompact hne hlocal
  let rimEquiv : ↥(S0 ∩ frontier R) ≃ₜ ↥(S ∩ O) :=
    { toFun := fun x => ⟨⟨x.val, hSF x.property.1⟩, (hrim _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val, (hrim x.val).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let rim : ↥(S0 ∩ frontier R) ≃ₜ frontier S :=
    rimEquiv.trans (Homeomorph.setCongr hboundary.symm)
  let phase : S ≃ₜ S0 :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hSF x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let positive : A.positive ≃ₜ S0 := (Homeomorph.setCongr hpos).trans phase
  let U : Set S0 := positive '' A.positive_range
  let c : (↥(S0 ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ U :=
    ((rim.prodCongr (Homeomorph.refl _)).trans A.positive_collar).trans
      (positive.image A.positive_range)
  refine ⟨U, positive.isOpenMap _ A.positive_open, c, ?_⟩
  intro x
  apply Subtype.ext
  change (((A.positive_collar (collarBase (rim x)) : A.positive) : frontier N) : X) = (x : X)
  exact congrArg (fun y : frontier N => (y : X)) (A.positive_base (rim x))

end PoincareConjecture.M76.HamiltonIntervalTorus
