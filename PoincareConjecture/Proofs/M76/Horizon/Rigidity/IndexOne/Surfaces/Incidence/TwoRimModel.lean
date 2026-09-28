import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.CompressedModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.Subcomplexes









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Q2" => Metric.sphere (0 : V2) 1

open Classical in


theorem exists_compressed_sourceSurface_two_rim_incidence_model
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (J : Bool → SimplicialComplex ℝ (s → ℝ × V3))
      (Hmodel : K.space ≃ₜ sourceSurface phi theta) (g : (s → ℝ × V3) → X)
      (j : ∀ side, Q2 ≃ₜ sourceRimCircle phi theta F0 (originalIntervalEndpoint side))
      (gamma : ∀ side, Q2 ≃ₜ (J side).space),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      K.space = F '' sourceSurface phi theta ∧
      A.space = F '' (sourceSurface phi theta ∩ frontier R) ∧
      (∀ x : sourceSurface phi theta, (Hmodel.symm x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (Hmodel z : X) = g z) ∧
      PolyhedralPLInCharts e g K.space ∧
      (∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ A.space) ∧
      (∀ t ∈ K.faces, (∀ w ∈ t, w ∈ A.vertices) → t ∈ A.faces) ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if ∃ side, t ∈ (J side).faces then 1 else 2) ∧
      (∀ w ∈ K.vertices, IsConnected (K.link w).space) ∧
      (sourceSurface phi theta).Nonempty ∧
      (∀ side, J side ≤ A ∧ J side ≤ K ∧ (J side).faces.Finite) ∧
      Pairwise (fun a b => Disjoint (J a).space (J b).space) ∧
      (⋃ side, (J side).space) = A.space ∧
      (∀ t, t ∈ A.faces ↔ ∃ side, t ∈ (J side).faces) ∧
      (∀ side, (J side).space = Set.range
        (fun z : sourceRimCircle phi theta F0 (originalIntervalEndpoint side) => F (z.val : X))) ∧
      (∀ side, (gamma side).IsFinitePL ∧ (gamma side).symm.IsFinitePL) ∧
      ∀ side x, (gamma side x : s → ℝ × V3) = F ((j side x).val : X) := by
  classical
  obtain ⟨s, F, K, A, Hmodel, g, hFc, hF, hFi, hK, hAK, hA, hKs, hAs,
    hHF, hHg, hgPL, hmark, hfull, hpure, hcounts, hlinks, hSne⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 heN hfront hAB hcorner
  obtain ⟨J, hJA, hdis, hcover, hfaces, hJs, j, gamma, hgamma, hval⟩ :=
    exists_sourceRim_finitePL_circle_subcomplexes_of_injOn
      hd phi hphi theta F0 F hFc hF (hFi.mono (sourceSurface_subset phi theta)) A hA hAs
  refine ⟨s, F, K, A, J, Hmodel, g, j, gamma, hFc, hF, hFi, hK, hAK, hA,
    hKs, hAs, hHF, hHg, hgPL, hmark, hfull, hpure, ?_, hlinks, hSne, ?_,
    hdis, hcover, hfaces, hJs, hgamma, hval⟩
  · intro t ht htc
    rw [hcounts t ht htc, hfaces t]
    split_ifs <;> rfl
  · intro side
    exact ⟨(hJA side).1, (hJA side).1.trans hAK, (hJA side).2⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
