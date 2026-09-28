import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.IncompressiblePhases

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.PhasePartition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.MarkedCoverInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.HandleInjection



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.HamiltonIntervalTorus
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem exists_complementary_sourcePhases_ambient_pi1_injective
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (eta : C(H, H)) (K : Set X), IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ K →
          eta x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta) ∧
        Nonempty (phi.HomotopyRel eta B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel eta B) ∧
        eta ⁻¹' B = phi ⁻¹' B ∧
        (∀ theta ∈ ({a, b} : Set ℝ), ∀ x : sourceSurface eta (theta : C),
          Function.Injective (FundamentalGroup.map
            (VanKampen.inclusion (sourceSurface eta (theta : C))) x)) ∧
        ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          let N := sourceSlab eta uv.1 uv.2
          IsCompact N ∧ ∃ _he : PLDomain e N,
            frontier N = (N ∩ frontier R) ∪
              (sourceSurface eta (uv.1 : C) ∪ sourceSurface eta (uv.2 : C)) ∧
            ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
              (∃ hSN : sourceSurface eta (theta : C) ⊆ N,
                ∀ x : sourceSurface eta (theta : C),
                  Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
              ∀ x ∈ sourceSurface eta (theta : C) ∩ frontier R,
                ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3)
                    (G : OpenPartialHomeomorph X V3),
                  psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧ lambda.contLinear v = 1 ∧
                  x ∈ G.source ∧ psi (G x) = 0 ∧
                  (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
                  (∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y)) ∧
                  (∀ y ∈ G.source, y ∈ N ∩ frontier R ↔
                    psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
                  ∀ y ∈ G.source, y ∈ sourceSurface eta (theta : C) ↔
                    psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : TopologicalSpace.MetrizableSpace
      ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.metrizableSpace
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨a, haI, b, hbI, eta, K, hK, hKR, hfixed, heta, Heta, ⟨Feta⟩, hB, hslabs⟩ :=
    exists_complementary_sourceSlabs_pi1_injective e d hd phi hphi F0
  have ha : 0 < a := by linarith [haI.1]
  have hab : a < b := by linarith [haI.2, hbI.1]
  have hb : b < p := by linarith [hbI.2]
  let A := sourceSurface eta (a : C)
  let B' := sourceSurface eta (b : C)
  let N := sourceSlab eta a b
  let M := sourceSlab eta b (a + p)
  obtain ⟨hcover, hmeet⟩ := sourceSlab_complementary_partition eta ha hab hb
  have hinj := marked_cover_phases_pi1_injective e
    (sourceSlab_subset eta a b) (sourceSlab_subset eta b (a + p))
    hcover hmeet
    ((sourceSurface_nonempty eta (a : C) Feta).mono subset_union_left)
    isClosed_frontier (sourceSurface_isCompact eta (a : C)).isClosed
    (sourceSurface_isCompact eta (b : C)).isClosed
    (sourceSurface_disjoint_of_ordered_phases eta ha hab hb) (by
      intro T hT
      obtain ⟨uv, huv, rfl⟩ : ∃ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          T = sourceSlab eta uv.1 uv.2 := by
        rcases hT with rfl | rfl
        · exact ⟨(a, b), Or.inl rfl, rfl⟩
        · exact ⟨(b, a + p), Or.inr rfl, rfl⟩
      obtain ⟨hTc, he, hf, hp⟩ := hslabs uv huv
      have hends : sourceSurface eta (uv.1 : C) ∪ sourceSurface eta (uv.2 : C) = A ∪ B' := by
        rcases huv with rfl | rfl
        · rfl
        · simp only [AddCircle.coe_add_period, A, B', union_comm]
      refine ⟨hTc, he, hf.trans (by rw [hends]), ?_⟩
      intro P hP
      obtain ⟨theta, htheta, rfl⟩ : ∃ theta ∈ ({uv.1, uv.2} : Set ℝ),
          P = sourceSurface eta (theta : C) := by
        rcases huv with rfl | rfl
        · rcases hP with rfl | rfl
          · exact ⟨a, Or.inl rfl, rfl⟩
          · exact ⟨b, Or.inr rfl, rfl⟩
        · rcases hP with rfl | rfl
          · exact ⟨a + p, Or.inr rfl, by simp only [AddCircle.coe_add_period]⟩
          · exact ⟨b, Or.inl rfl, rfl⟩
      refine ⟨(hp theta htheta).1, ?_⟩
      intro x hx
      obtain ⟨psi, lambda, w, v, G, hpw, hpv, hlv, hxG, _, _, hGT, _, hGP⟩ :=
        (hp theta htheta).2 x hx
      exact ⟨psi, lambda, w, v, G, hpw, hpv, hlv, hxG, hGT, hGP⟩)
  refine ⟨a, haI, b, hbI, eta, K, hK, hKR, hfixed, heta, Heta, ⟨Feta⟩, hB, ?_, hslabs⟩
  intro theta htheta x
  have hP : sourceSurface eta (theta : C) ∈ ({A, B'} : Set (Set X)) := by
    rcases htheta with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hPR, hpi⟩ := hinj _ hP
  have heq : VanKampen.inclusion (sourceSurface eta (theta : C)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)).comp (ContinuousMap.inclusion hPR) := rfl
  rw [heq, FundamentalGroup.map_comp]
  exact (handle_ambient_pi1_injective _).comp (hpi x)
end PoincareConjecture.M76.HamiltonIntervalTorus
