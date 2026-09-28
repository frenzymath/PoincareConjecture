import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.PairedCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.SourceMeridian









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



structure PairedMeridianHierarchy {α β : Type*}
    (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H)) where
  a : ℝ
  b : ℝ
  a_range : a ∈ Ioo (p / 4) (p / 3)
  b_range : b ∈ Ioo (2 * p / 3) (3 * p / 4)
  eta : C(H, H)
  support : Set X
  identity_homotopy : (ContinuousMap.id H).HomotopyRel eta B
  support_compact : IsCompact support
  support_interior : support ⊆ interior R
  fixed_off_support : ∀ x : H,
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ support → eta x = phi x
  original_pl : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta)
  relative_homotopy : Nonempty (phi.HomotopyRel eta B)
  boundary_preimage : eta ⁻¹' B = phi ⁻¹' B
  geometry : PairedSourceGeometry e eta a b
  slab_irreducible : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
    IsPLIrreducible e (sourceSlab eta uv.1 uv.2)
  annuli : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface eta theta
  parametrizations : ∀ theta ∈ ({(a : C), (b : C)} : Set C), ℝ × ℝ → X
  parametrizations_pl : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)),
    PolyhedralPLInCharts e (parametrizations theta htheta) Ann
  annuli_exact : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)) (x : Ann),
    (annuli theta htheta x : X) = parametrizations theta htheta x
  rim_marks : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)) side z,
    (annuli theta htheta (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle eta theta identity_homotopy (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side)
        (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
          (by norm_num) (by norm_num) z) : X)
  annuli_homotopies : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)),
    Nonempty ((sourceAnnulusHandleMap eta theta (annuli theta htheta)).HomotopyRel
      (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
      Dehn.annulusRims)
  meridians : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
    ∃ E : ↥(frontier (sourceSlab eta uv.1 uv.2)) ≃ₜ
        ↥(frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2)),
      (∀ x : frontier (sourceSlab eta uv.1 uv.2),
        (x : X) ∈ frontier R → (E x : X) = x) ∧
      (∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (x : sourceSurface eta theta) (hx : (x : X) ∈ frontier (sourceSlab eta uv.1 uv.2)),
        (E ⟨x, hx⟩ : X) = standardTargetAnnulus theta ((annuli theta htheta).symm x)) ∧
      Nonempty ((eta.comp (slabFrontierHandleInclusion eta uv.1 uv.2)).HomotopyRel
        ((slabFrontierHandleInclusion (ContinuousMap.id H) uv.1 uv.2).comp ⟨E, E.continuous⟩)
        {x | (x : X) ∈ frontier R}) ∧
      ∃ (retract : C(frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2), Q))
        (j : V2 → X) (rim : C(Q, frontier (sourceSlab eta uv.1 uv.2))),
        PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧
        MapsTo j D (sourceSlab eta uv.1 uv.2) ∧
        (∀ x : Q, j x = (rim x : X)) ∧
        (∀ x : D, j x ∈ frontier (sourceSlab eta uv.1 uv.2) ↔ (x : V2) ∈ Q) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Dehn.squareRimLoop.map rim.continuous).map
            (retract.comp ⟨E, E.continuous⟩).continuous)) ≠ 1



theorem exists_original_paired_meridian_hierarchy
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    Nonempty (PairedMeridianHierarchy e d phi) := by
  classical
  obtain ⟨a, ha, b, hb, eta, K, Feta, hK, hKR, hfixed, heta, Heta, hB,
      geometry, hirr, hannuli⟩ :=
    exists_relative_corrected_whole_source_annuli e d hd phi hphi hI F0
  have hcannuli : ∀ theta ∈ ({(a : C), (b : C)} : Set C),
      ∃ (A : Ann ≃ₜ sourceSurface eta theta) (q : ℝ × ℝ → X),
        PolyhedralPLInCharts e q Ann ∧ (∀ x : Ann, (A x : X) = q x) ∧
        (∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
          (sourceBoundaryCircle eta theta Feta (originalIntervalEndpoint side)
            (originalIntervalEndpoint_norm side)
            (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
              (by norm_num) (by norm_num) z) : X)) ∧
        Nonempty ((sourceAnnulusHandleMap eta theta A).HomotopyRel
          (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
          Dehn.annulusRims) := by
    intro theta htheta
    rcases htheta with rfl | rfl
    · exact hannuli a (Or.inl rfl)
    · exact hannuli b (Or.inr rfl)
  choose A q hq hA hmarks hhom using hcannuli
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  refine ⟨{
    a := a, b := b, a_range := ha, b_range := hb
    eta := eta, support := K, identity_homotopy := Feta
    support_compact := hK, support_interior := hKR, fixed_off_support := hfixed
    original_pl := heta, relative_homotopy := Heta, boundary_preimage := hB
    geometry := geometry, slab_irreducible := hirr
    annuli := A, parametrizations := q, parametrizations_pl := hq
    annuli_exact := hA, rim_marks := hmarks, annuli_homotopies := hhom
    meridians := ?_ }⟩
  intro uv huv
  have hphases : ({(uv.1 : C), (uv.2 : C)} : Set C) = {(a : C), (b : C)} := by
    rcases huv with rfl | rfl
    · rfl
    · simp only [AddCircle.coe_add_period]
      exact pair_comm _ _
  let Auv : ∀ theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C),
      Ann ≃ₜ sourceSurface eta theta := fun theta htheta => A theta (hphases ▸ htheta)
  have hmarksuv : ∀ theta (htheta : theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C)),
      ∀ side z, (Auv theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle eta theta Feta (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
            (by norm_num) (by norm_num) z) : X) := fun theta htheta => hmarks theta _
  have hhomuv : ∀ theta (htheta : theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C)),
      Nonempty ((sourceAnnulusHandleMap eta theta (Auv theta htheta)).HomotopyRel
        (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
        Dehn.annulusRims) := fun theta htheta => hhom theta _
  have hc : ∃ c : ℝ, c < uv.1 ∧ uv.1 < uv.2 ∧ uv.2 < c + p := by
    rcases huv with rfl | rfl
    · exact ⟨0, ha0, hab, by simpa using hbp⟩
    · refine ⟨(a + b) / 2, ?_, ?_, ?_⟩ <;> dsimp <;> linarith
  obtain ⟨c, hca, huvlt, hvc⟩ := hc
  obtain ⟨E, hEold, hEphase, hEhom, disks⟩ :=
    exists_source_slab_meridian_disk e eta Feta hca huvlt hvc
      (geometry.domains uv huv)
      (geometry.slab_ambient_pi1_injective Feta ha0 hab hbp uv huv)
      (geometry.frontiers uv huv) Auv hmarksuv hhomuv
  refine ⟨E, hEold, ?_, hEhom, disks⟩
  intro theta htheta x hx
  exact hEphase theta (hphases.symm ▸ htheta) x

end PoincareConjecture.M76.HamiltonIntervalTorus
