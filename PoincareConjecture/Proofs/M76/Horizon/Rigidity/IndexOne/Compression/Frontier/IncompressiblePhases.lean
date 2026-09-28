import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.MinimalComplementary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.ComplementarySourceSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.TransverseCorners
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.PhaseMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.KernelInjection

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

theorem exists_complementary_sourceSlabs_pi1_injective
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
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  obtain ⟨a, haI, b, hbI, _, he, hf, _, he', hf', _, _, _, _, hcorners⟩ :=
    exists_complementary_sourceSlabs_with_transverse_corners e d hd phi hphi F0
  have ha : 0 < a := by linarith [haI.1]
  have hab : a < b := by linarith [haI.2, hbI.1]
  have hb : b < p := by linarith [hbI.2]
  obtain ⟨eta, K, hK, hKR, hfixed, heta, Heta, ⟨Feta⟩, hB, hslabs⟩ :=
    exists_complementary_sourceSlabs_frontier_kernels_at e d hd phi hphi F0 ha hab hb he he' hf hf'
  have habq : (a : C) ≠ (b : C) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  have hdis : Disjoint (sourceSurface eta (a : C)) (sourceSurface eta (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    exact disjoint_left.mpr (fun _ hx hy => habq (hx.2.symm.trans hy.2))
  refine ⟨a, haI, b, hbI, eta, K, hK, hKR, hfixed, heta, Heta, ⟨Feta⟩, hB, ?_⟩
  intro uv huv
  obtain ⟨hN, heN, hfront, hkernel⟩ := hslabs uv huv
  refine ⟨hN, heN, hfront, ?_⟩
  intro theta htheta
  have hcorner := fun x (hx : x ∈ sourceSurface eta (theta : C) ∩ frontier R) => by
    have hxK : x ∉ K := fun h => hx.2.2 (hKR h)
    have hxphi : x ∈ sourceSurface phi (theta : C) :=
      (sourceSurface_agrees_off_support phi eta hfixed (theta : C) x hxK).mp hx.1
    exact exists_transverse_marked_corner_of_supported_map e phi eta hK.isClosed hKR hfixed
      uv.1 uv.2 (theta : C) hx.2 (hcorners uv huv theta htheta x ⟨hxphi, hx.2⟩)
  refine ⟨?_, hcorner⟩
  have hpair : Disjoint (sourceSurface eta (uv.1 : C)) (sourceSurface eta (uv.2 : C)) := by
    rcases huv with huv | huv
    · rw [show uv = (a, b) from huv]
      exact hdis
    · rw [show uv = (b, a + p) from huv]
      simpa only [AddCircle.coe_add_period] using hdis.symm
  obtain ⟨other, hfrontTheta, hdisTheta⟩ :
      ∃ other : C,
        frontier (sourceSlab eta uv.1 uv.2) =
          (sourceSlab eta uv.1 uv.2 ∩ frontier R) ∪
            (sourceSurface eta (theta : C) ∪ sourceSurface eta other) ∧
          Disjoint (sourceSurface eta (theta : C)) (sourceSurface eta other) := by
    rcases htheta with ht | ht
    · change theta = uv.1 at ht
      rw [ht]
      exact ⟨(uv.2 : C), hfront, hpair⟩
    · change theta = uv.2 at ht
      rw [ht]
      exact ⟨(uv.1 : C), by simpa only [union_comm] using hfront, hpair.symm⟩
  have hcorner' : ∀ x ∈ sourceSurface eta (theta : C) ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ sourceSlab eta uv.1 uv.2 ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab eta uv.1 uv.2 ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface eta (theta : C) ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
    intro x hx
    obtain ⟨psi, lambda, w, z, G, hpw, hpz, hlz, hxG, _, _, hGN, hGO, hGS⟩ := hcorner x hx
    exact ⟨psi, lambda, w, z, G, hpw, hpz, hlz, hxG, hGN, hGO, hGS⟩
  obtain ⟨hSF, hpi⟩ := sourcePhase_frontier_pi1_injective e eta Feta heN
    hfrontTheta hdisTheta hcorner'
  obtain ⟨D, hzero, hkeep, hend⟩ := exists_sourcePhase_inward_motion e eta Feta heN
    hfrontTheta hdisTheta hcorner'
  obtain ⟨hMF, hker⟩ := hkernel theta htheta
  exact sourcePhase_slab_pi1_injective_of_motion eta heN hSF hpi D hzero hkeep hend hMF hker

end PoincareConjecture.M76.HamiltonIntervalTorus
