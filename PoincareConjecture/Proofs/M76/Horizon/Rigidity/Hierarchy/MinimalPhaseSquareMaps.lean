import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.MinimalFiberwisePhaseProducts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Recognition.OriginalCollar







set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_minimal_phase_square_maps {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ n, (∀ m, HamiltonZeroIncompressiblePhaseCount e d phi m → n ≤ m) ∧
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ psi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        let q := hamiltonZeroCircleMap psi
        let R := q ⁻¹' AddCircle.closedIntervalArc p a b
        PLDomain e R ∧ frontier R = q ⁻¹' {(a : C0), (b : C0)} ∧
        IsPLIrreducible e R ∧ IsPLIrreducible e (interior R)ᶜ ∧
        (∀ x : frontier R, Function.Injective
          (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) ∧
        (∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)), ∀ x : T,
          Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x)) ∧
        (∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
          ∀ x : q ⁻¹' {theta}, Function.Injective (FundamentalGroup.map
            (VanKampen.inclusion (q ⁻¹' {theta})) x)) ∧
        (∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          lower.count + upper.count = n ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x))) ∧
        ∃ (s : Finset R) (rho : ℝ), 0 < rho ∧
          ∀ theta ∈ ({a, b} : Set ℝ),
            ∃ (J : SimplicialComplex ℝ (s → ℝ × V3))
              (H : J.space ≃ₜ (q ⁻¹' {(theta : C0)} : Set X0))
              (c : (s → ℝ × V3) × ℝ → X0),
              J.faces.Finite ∧
              PolyhedralPLInCharts e c (J.space ×ˢ Icc (-rho) rho) ∧
              IsEmbedding (fun z : J.space ×ˢ Icc (-rho) rho => c z) ∧
              (∀ x : J.space, c ((x : s → ℝ × V3), 0) = H x) ∧
              (∀ eps : ℝ, 0 < eps → eps ≤ rho →
                IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps))) ∧
              (∀ x : J.space, ∀ t ∈ Icc (-rho) rho,
                Q0 (hamiltonZeroAmbientMap psi (c ((x : s → ℝ × V3), t))) =
                  ((Q0 (hamiltonZeroAmbientMap psi (H x))).1,
                    (theta : C0) + (((if theta = a then 1 else -1) * t : ℝ) : C0))) ∧
              ∃ u : J.vertexAbstractComplex.edgeGraph.ConnectedComponent →
                  (ℝ × ℝ) → (s → ℝ × V3),
                ∀ D, FinitePiecewiseAffineOn (u D) (Icc 0 64 ×ˢ Icc 0 64) ∧
                  u D '' (Icc 0 64 ×ˢ Icc 0 64) = (J.edgeComponentComplex D).space ∧
                  ∀ z w : PeriodicSquare.Square 64,
                    u D (z.1, z.2) = u D (w.1, w.2) ↔
                      PeriodicSquare.projection 64 z = PeriodicSquare.projection 64 w := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  obtain ⟨n, hmin, a, ha, b, hb, psi, hpsi, Hpsi, Fpsi,
    he, hfront, _, _, hIR, hIS, hfrontInj, hsides, hphases,
    ⟨Nlower, Nupper, lower, upper, hcount, hnoA, hnoB, hntA, hntB⟩,
    s, rho, hrho, hproducts⟩ :=
    exists_hamiltonZero_minimal_fiberwise_phase_products e d hI hd phi hphi F
  have hab : a < b := by linarith [ha.2, hb.1]
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [ha.1, ha.2]
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [hb.1, hb.2]
  have hne : (a : C0) ≠ (b : C0) :=
    fun h => hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h)
  have hclosed (t : C0) : IsClosed (hamiltonZeroCircleMap psi ⁻¹' {t}) :=
    isClosed_singleton.preimage (hamiltonZeroCircleMap psi).continuous
  have hdis : Disjoint (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)})
      (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) := by
    exact (disjoint_singleton.mpr hne).preimage _
  have hsplit : frontier (hamiltonZeroCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p a b) =
      (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}) ∪
        (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) := by
    rw [hfront]
    ext x
    simp
  refine ⟨n, hmin, a, ha, b, hb, psi, hpsi, Hpsi, Fpsi,
    he, hfront, hIR, hIS, hfrontInj, hsides,
    (fun theta htheta x => (hphases theta htheta x).1),
    ⟨Nlower, Nupper, lower, upper, hcount, hnoA, hnoB, hntA, hntB⟩,
    s, rho, hrho, ?_⟩
  intro theta htheta
  obtain ⟨J, H, c, K, hJ, _, hKs, hc, hi, hzero, hopen, _, hproduct, _⟩ :=
    hproducts theta htheta
  have hc' : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-rho) rho) := hKs ▸ hc
  have hi' : IsEmbedding (fun z : J.space ×ˢ Icc (-rho) rho => c z) := by
    exact hi.comp ((Homeomorph.setCongr hKs.symm).isEmbedding)
  refine ⟨J, H, c, hJ, hc', hi', hzero, hopen, hproduct, ?_⟩
  rcases htheta with htheta | htheta
  · have htheta' : theta = a := htheta
    subst theta
    exact he.exists_square_maps_on_original_phase_collar he.closed.isCompact
      (hclosed a) (hclosed b) hdis hsplit lower hntA hfrontInj
      J hJ hrho.le c hc' H hzero
  · have htheta' : theta = b := htheta
    subst theta
    exact he.exists_square_maps_on_original_phase_collar he.closed.isCompact
      (hclosed b) (hclosed a) hdis.symm (hsplit.trans (union_comm _ _)) upper hntB hfrontInj
      J hJ hrho.le c hc' H hzero

end PoincareConjecture.M76
