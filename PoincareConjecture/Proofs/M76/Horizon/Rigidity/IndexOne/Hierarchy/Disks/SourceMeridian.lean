import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.Homotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.SlabInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.FrontierComparison
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.StandardMeridian

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

theorem slab_frontier_ambient_homotopic
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (a b : ℝ)
    (E : ↥(frontier (sourceSlab phi a b)) ≃ₜ
      ↥(frontier (sourceSlab (ContinuousMap.id H) a b)))
    (G : (phi.comp (slabFrontierHandleInclusion phi a b)).HomotopyRel
      ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp ⟨E, E.continuous⟩)
      {x | (x : X) ∈ frontier R}) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier (sourceSlab phi a b), X)).Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(frontier (sourceSlab (ContinuousMap.id H) a b), X)).comp ⟨E, E.continuous⟩) := by
  let j : C(H, X) := ⟨fun x => ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X),
    by fun_prop⟩
  have hstart : (slabFrontierHandleInclusion phi a b).Homotopic
      (phi.comp (slabFrontierHandleInclusion phi a b)) :=
    (show (ContinuousMap.id H).Homotopic phi from ⟨F.toHomotopy⟩).comp
      (.refl (slabFrontierHandleInclusion phi a b))
  have hh := (ContinuousMap.Homotopic.refl j).comp (hstart.trans ⟨G.toHomotopy⟩)
  have hleft : j.comp (slabFrontierHandleInclusion phi a b) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier (sourceSlab phi a b), X)) := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm_apply_apply _)
  have hright : j.comp ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp
      ⟨E, E.continuous⟩) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(frontier (sourceSlab (ContinuousMap.id H) a b), X)).comp ⟨E, E.continuous⟩ := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm_apply_apply _)
  rwa [hleft, hright] at hh

theorem exists_source_slab_meridian_disk
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hN : PLDomain e (sourceSlab phi a b))
    (hinj : ∀ x : sourceSlab phi a b, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSlab phi a b, X)) x))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (hA : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)), ∀ side z,
      (A theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
            (by norm_num) (by norm_num) z) : X))
    (hhom : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)),
      Nonempty ((sourceAnnulusHandleMap phi theta (A theta htheta)).HomotopyRel
        (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
        Dehn.annulusRims)) :
    ∃ E : ↥(frontier (sourceSlab phi a b)) ≃ₜ
        ↥(frontier (sourceSlab (ContinuousMap.id H) a b)),
      (∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x) ∧
      (∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (x : sourceSurface phi theta),
        (E ⟨x, hfront.symm ▸ Or.inr (by
          rcases htheta with rfl | rfl
          · exact Or.inl x.property
          · exact Or.inr x.property)⟩ : X) =
          standardTargetAnnulus theta ((A theta htheta).symm x)) ∧
      Nonempty ((phi.comp (slabFrontierHandleInclusion phi a b)).HomotopyRel
        ((slabFrontierHandleInclusion (ContinuousMap.id H) a b).comp ⟨E, E.continuous⟩)
        {x | (x : X) ∈ frontier R}) ∧
      ∃ (retract : C(frontier (sourceSlab (ContinuousMap.id H) a b), Q))
        (j : V2 → X) (rim : C(Q, frontier (sourceSlab phi a b))),
        PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧
        MapsTo j D (sourceSlab phi a b) ∧
        (∀ x : Q, j x = (rim x : X)) ∧
        (∀ x : D, j x ∈ frontier (sourceSlab phi a b) ↔ (x : V2) ∈ Q) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Dehn.squareRimLoop.map rim.continuous).map
            (retract.comp ⟨E, E.continuous⟩).continuous)) ≠ 1 := by
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  obtain ⟨E, hEold, hEphase, ⟨G⟩⟩ := exists_original_to_standard_frontier_homotopy
    phi F ha hab hb hfront A hA hhom
  have hshort : b < a + p := by linarith
  obtain ⟨targetDisk, targetRim, retract, hboundary, hleft, _⟩ :=
    exists_standard_meridian a b hab hshort
  obtain ⟨j, rim, hj, hi, hmap, hbd, hproper, hess⟩ :=
    exists_proper_disk_of_frontier_comparison e hN hinj E
      (slab_frontier_ambient_homotopic phi F a b E G)
      targetDisk targetRim hboundary retract hleft
  exact ⟨E, hEold, hEphase, ⟨G⟩, retract, j, rim, hj, hi, hmap, hbd, hproper, hess⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
