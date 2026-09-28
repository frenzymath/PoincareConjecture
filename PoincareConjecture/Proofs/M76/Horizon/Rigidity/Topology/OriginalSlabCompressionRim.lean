import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleSlab

set_option autoImplicit false

open Set Geometry Metric

namespace PoincareConjecture.M76

theorem isOpen_boundary_phase_of_frontier_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (q : C(X, Y)) {R : Set X} {a b theta : Y} (hab : a ≠ b)
    (hfront : frontier R = q ⁻¹' {a, b}) (htheta : theta ∈ ({a, b} : Set Y)) :
    IsOpen ((Subtype.val : frontier R → X) ⁻¹' (q ⁻¹' {theta})) := by
  have first (a b : Y) (hab : a ≠ b) (hfront : frontier R = q ⁻¹' {a, b}) :
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' (q ⁻¹' {a})) := by
    have heq : (Subtype.val : frontier R → X) ⁻¹' (q ⁻¹' {a}) =
        ((fun x : frontier R => q x) ⁻¹' {b})ᶜ := by
      ext x
      have hx : q x = a ∨ q x = b := by
        have hmem := hfront.subset x.property
        simpa only [mem_preimage, mem_insert_iff, mem_singleton_iff] using hmem
      change q x = a ↔ q x ≠ b
      constructor
      · intro hqa hqb
        exact hab (hqa.symm.trans hqb)
      · intro hqb
        exact hx.resolve_right hqb
    rw [heq]
    exact (isClosed_singleton.preimage (q.continuous.comp continuous_subtype_val)).isOpen_compl
  rcases htheta with htheta | htheta
  · change theta = a at htheta
    subst theta
    exact first a b hab hfront
  · change theta = b at htheta
    subst theta
    exact first b a hab.symm (by simpa only [pair_comm] using hfront)

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem exists_hamiltonZero_slab_compression_rim_alternative {ι κ : Type*}
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
                  ∃ (gamma : C(Q, M)) (f : C(D, T)),
                    gamma Dehn.squareRimBase = x ∧
                    (∀ z : Q, (f ⟨z, sphere_subset_closedBall z.property⟩ : X0) =
                      (gamma z : X0)) ∧
                    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
                      (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  obtain ⟨a, haI, b, hbI, ha, hab, hb, _, _, _, _, _,
    hR, he, hfront, hminus, heminus, hfrontminus, _, _, _⟩ :=
    exists_hamiltonZero_regular_circle_slab e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hR, he, hfront,
    hminus, heminus, hfrontminus, ?_⟩
  intro T hT theta htheta
  have hTfront : frontier T = (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0), (b : C0)} := by
    rcases hT with hT | hT
    · exact hT ▸ hfront
    · exact hT ▸ hfrontminus
  have hTclosed : IsClosed T := by
    rcases hT with hT | hT
    · exact hT ▸ he.closed
    · exact hT ▸ heminus.closed
  have hMfront : (hamiltonZeroCircleMap phi) ⁻¹' {theta} ⊆ frontier T := by
    intro y hy
    rw [hTfront]
    change hamiltonZeroCircleMap phi y ∈ ({(a : C0), (b : C0)} : Set C0)
    change hamiltonZeroCircleMap phi y = theta at hy
    rw [hy]
    exact htheta
  have hMT := hMfront.trans hTclosed.frontier_subset
  have habC : (a : C0) ≠ (b : C0) := by
    intro h
    have haP : a ∈ Ico (0 : ℝ) (0 + 4 * 16) := ⟨ha.le, by linarith⟩
    have hbP : b ∈ Ico (0 : ℝ) (0 + 4 * 16) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haP hbP).mp h)
  refine ⟨hMT, hMfront,
    isOpen_boundary_phase_of_frontier_eq (hamiltonZeroCircleMap phi) habC hTfront htheta, ?_⟩
  intro x
  rcases Dehn.injective_or_exists_squareRim_filling (ContinuousMap.inclusion hMT) x
    with hinj | ⟨gamma, f, hbase, hf, hnontrivial⟩
  · exact Or.inl hinj
  · exact Or.inr ⟨gamma, f, hbase, fun z => congrArg Subtype.val (hf z), hnontrivial⟩

end PoincareConjecture.M76
