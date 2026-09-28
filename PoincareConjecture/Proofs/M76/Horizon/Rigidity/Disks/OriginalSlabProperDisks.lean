import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.OriginalSlabCompressionRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage












set_option autoImplicit false

open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1



theorem injective_or_exists_marked_proper_disk
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    (e : α → OpenPartialHomeomorph X V3) {R M : Set X}
    (he : PLDomain e R) (hMT : M ⊆ R) (hMfront : M ⊆ frontier R)
    (hMopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' M)) (x : M) :
    Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMT) x) ∨
      ∃ (j : V2 → X) (rim : C(Q, M)),
        PolyhedralPLInCharts e j D ∧
        Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D R ∧
        (∀ z : Q, j z = (rim z : X)) ∧
        (∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) ∧
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  obtain hinj | ⟨gamma, f, _, hf, hnontrivial⟩ :=
    Dehn.injective_or_exists_squareRim_filling (ContinuousMap.inclusion hMT) x
  · exact Or.inl hinj
  · exact Or.inr (Dehn.exists_marked_boundary_disk_with_essential_image
      e R he M hMfront hMopen f gamma (fun z => congrArg Subtype.val (hf z))
      (ContinuousMap.id M) hnontrivial)

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩




theorem exists_hamiltonZero_slab_proper_disk_alternative {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ a ∈ Ioo ((4 * 16 : ℝ) / 4) ((4 * 16 : ℝ) / 3),
      ∃ b ∈ Ioo (2 * (4 * 16 : ℝ) / 3) (3 * (4 * 16 : ℝ) / 4),
        0 < a ∧ a < b ∧ b < 4 * 16 ∧
        let q := hamiltonZeroCircleMap phi
        let R := q ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
        let S := q ⁻¹' {(a : C0), (b : C0)}
        IsCompact R ∧ PLDomain e R ∧ frontier R = S ∧
        IsCompact (interior R)ᶜ ∧ PLDomain e (interior R)ᶜ ∧
        frontier (interior R)ᶜ = S ∧
        ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)),
          ∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
            let M := q ⁻¹' {theta}
            ∃ hMT : M ⊆ T,
              M ⊆ frontier T ∧
              IsOpen ((Subtype.val : frontier T → X0) ⁻¹' M) ∧
              ∀ x : M,
                Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMT) x) ∨
                  ∃ (j : V2 → X0) (rim : C(Q, M)),
                    PolyhedralPLInCharts e j D ∧
                    Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D T ∧
                    (∀ z : Q, j z = (rim z : X0)) ∧
                    (∀ z : D, j z ∈ frontier T ↔ (z : V2) ∈ Q) ∧
                    FundamentalGroup.fromPath
                      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨a, haI, b, hbI, ha, hab, hb,
    hR, he, hfront, hminus, heminus, hfrontminus, hAlt⟩ :=
    exists_hamiltonZero_slab_compression_rim_alternative e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hR, he, hfront,
    hminus, heminus, hfrontminus, ?_⟩
  intro T hT theta htheta
  obtain ⟨hMT, hMfront, hMopen, _⟩ := hAlt T hT theta htheta
  refine ⟨hMT, hMfront, hMopen, ?_⟩
  intro x
  have heT : PLDomain e T := by
    rcases hT with hT | hT
    · exact hT ▸ he
    · exact hT ▸ heminus
  exact injective_or_exists_marked_proper_disk e heT hMT hMfront hMopen x

end PoincareConjecture.M76
