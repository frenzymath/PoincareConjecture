import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.PhaseInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.InwardMotion









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

private instance : Fact (0 < (4 * (128 : ℝ))) := ⟨by norm_num⟩



theorem exists_sourcePhase_inward_motion
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
    let A : Set (sourceSurface phi theta) :=
      {x | (x : X) ∉ frontier R}
    ∃ D : C(unitInterval × sourceSurface phi theta, sourceSurface phi theta),
      (∀ x, D (0, x) = x) ∧
      (∀ t, MapsTo (fun x => D (t, x)) A A) ∧
      ∀ x, D (1, x) ∈ A := by
  classical
  let : TopologicalSpace.MetrizableSpace
      ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let N := sourceSlab phi u v
  let S0 := sourceSurface phi theta
  let S : Set (frontier N) := Subtype.val ⁻¹' S0
  let O : Set (frontier N) := Subtype.val ⁻¹'
    ((N ∩ frontier R) ∪ sourceSurface phi theta')
  obtain ⟨hSF, hSc, hOc, hcover, hrim, hcompact, hne, hlocal⟩ :=
    sourcePhase_frontier_signed_data e phi F he hfront hdis hcorner
  obtain ⟨hfrontS, hother, U, hU, _, K, hbase, hpos, hneg, _⟩ :=
    exists_bicollar_of_signed_rim_charts hSc hOc hcover hcompact hne hlocal
  have hneg' : ∀ z, (K z : frontier N) ∈ (interior S)ᶜ ↔ (z.2 : ℝ) ≤ 0 := by
    simpa only [hother] using hneg
  obtain ⟨D, hzero, hpres, hpresint, hend⟩ :=
    exists_inward_motion_of_open_bicollar hSc (hfrontS.symm ▸ hcompact)
      hU K hbase hpos hneg'
  let E : S0 ≃ₜ S :=
    { toFun := fun x => ⟨⟨x.val, hSF x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hinter (y : S) : (y : frontier N) ∈ interior S ↔
      (E.symm y : X) ∉ frontier R := by
    rw [mem_interior_iff_notMem_frontier y.property, hfrontS, hrim]
    change (¬((y.val : X) ∈ S0 ∧ (y.val : X) ∈ frontier R)) ↔
      (y.val : X) ∉ frontier R
    exact not_congr (and_iff_right (show (y.val : X) ∈ S0 from y.property))
  let DS : C(unitInterval × S, S) :=
    ⟨fun z => ⟨D (z.1, z.2), hpres z.1 z.2.property⟩,
      (D.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
  let D0 : C(unitInterval × S0, S0) :=
    ⟨fun z => E.symm (DS (z.1, E z.2)),
      E.symm.continuous.comp (DS.continuous.comp
        (continuous_fst.prodMk (E.continuous.comp continuous_snd)))⟩
  refine ⟨D0, ?_, ?_, ?_⟩
  · intro x
    have hz : DS (0, E x) = E x := Subtype.ext (hzero _)
    change E.symm (DS (0, E x)) = x
    rw [hz, E.symm_apply_apply]
  · intro t x hx
    have hx' : ((E x : S) : frontier N) ∈ interior S := by
      apply (hinter (E x)).mpr
      simpa only [E.symm_apply_apply, mem_ofPred_eq] using hx
    exact (hinter (DS (t, E x))).mp (hpresint t hx')
  · intro x
    exact (hinter (DS (1, E x))).mp (hend (E x).property)

end PoincareConjecture.M76.HamiltonIntervalTorus
