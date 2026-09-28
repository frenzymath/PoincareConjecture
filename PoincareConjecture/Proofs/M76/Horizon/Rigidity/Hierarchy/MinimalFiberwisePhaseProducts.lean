import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.OriginalPhaseGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.MinimalFirstPhaseComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.PrescribedFiberwiseProducts

set_option autoImplicit false
open Set Geometry

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

theorem exists_hamiltonZero_minimal_fiberwise_phase_products {ι κ : Type*}
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
        let arc := AddCircle.closedIntervalArc p a b
        let R := q ⁻¹' arc
        PLDomain e R ∧ frontier R = q ⁻¹' {(a : C0), (b : C0)} ∧
        q ⁻¹' interior arc = interior R ∧
        q ⁻¹' (interior arc)ᶜ = (interior R)ᶜ ∧
        IsPLIrreducible e R ∧ IsPLIrreducible e (interior R)ᶜ ∧
        (∀ x : frontier R, Function.Injective
          (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) ∧
        (∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)), ∀ x : T,
          Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x)) ∧
        (∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
          ∀ x : q ⁻¹' {theta},
            Function.Injective (FundamentalGroup.map
              (VanKampen.inclusion (q ⁻¹' {theta})) x) ∧
            Function.Injective (FundamentalGroup.map (hamiltonZeroPhaseMap psi theta) x)) ∧
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
              (c : (s → ℝ × V3) × ℝ → X0)
              (K : SimplicialComplex ℝ ((s → ℝ × V3) × ℝ)),
              J.faces.Finite ∧ K.faces.Finite ∧
              K.space = J.space ×ˢ Icc (-rho) rho ∧
              PolyhedralPLInCharts e c K.space ∧
              Topology.IsEmbedding (fun z : K.space => c z) ∧
              (∀ x : J.space, c ((x : s → ℝ × V3), 0) = H x) ∧
              (∀ eps : ℝ, 0 < eps → eps ≤ rho →
                IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps))) ∧
              (∀ x ∈ J.space, ∀ t ∈ Icc (-rho) rho,
                q (c (x, t)) = (theta : C0) +
                  (((if theta = a then 1 else -1) * t : ℝ) : C0)) ∧
              (∀ x : J.space, ∀ t ∈ Icc (-rho) rho,
                Q0 (hamiltonZeroAmbientMap psi (c ((x : s → ℝ × V3), t))) =
                  ((Q0 (hamiltonZeroAmbientMap psi (H x))).1,
                    (theta : C0) + (((if theta = a then 1 else -1) * t : ℝ) : C0))) ∧
              q ⁻¹' AddCircle.closedIntervalArc p (theta - rho) (theta + rho) =
                c '' K.space := by
  obtain ⟨n, hcandidate, hmin⟩ :=
    exists_hamiltonZero_minimal_incompressible_phase_count e d hI hd phi hphi F
  obtain ⟨a, ha, b, hb, phi', hphi', ⟨H⟩, ⟨F'⟩, he, hfront,
    hirrR, hirrS, hfrontAmbient, hsides, Nlower, Nupper, lower, upper,
    hcount, hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩ := hcandidate
  have hphases := hamiltonZero_phase_injections_of_frontier
    phi' F' ha hb hfront hfrontAmbient
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hb64 : b < p := by linarith [hb.2]
  obtain ⟨psi, hpsi, ⟨G⟩, ⟨Fpsi⟩, hA, hB, hR, hinterior, hexterior,
    s, rho, hrho, hproducts⟩ :=
    exists_hamiltonZero_prescribed_fiberwise_products
      e d hd phi' hphi' F' a b ha0 hab hb64 he hfront
  have hphase (theta : C0) (htheta : theta ∈ ({(a : C0), (b : C0)} : Set C0)) :
      hamiltonZeroCircleMap psi ⁻¹' {theta} = hamiltonZeroCircleMap phi' ⁻¹' {theta} := by
    rcases htheta with rfl | rfl
    · exact hA
    · exact hB
  have hpair : hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} =
      hamiltonZeroCircleMap phi' ⁻¹' {(a : C0), (b : C0)} := by
    rw [show ({(a : C0), (b : C0)} : Set C0) = {(a : C0)} ∪ {(b : C0)} by
      ext; simp [or_comm]]
    rw [preimage_union, preimage_union, hA, hB]
  refine ⟨n, hmin, a, ha, b, hb, psi, hpsi, ⟨H.trans G⟩, ⟨Fpsi⟩, ?_⟩
  dsimp only
  rw [hR]
  refine ⟨he, hfront.trans hpair.symm, hinterior, hexterior,
    hirrR, hirrS, hfrontAmbient, hsides, ?_, ?_, s, rho, hrho, ?_⟩
  · intro theta htheta x
    have hi : ∀ x : hamiltonZeroCircleMap psi ⁻¹' {theta}, Function.Injective
        (FundamentalGroup.map
          (VanKampen.inclusion (hamiltonZeroCircleMap psi ⁻¹' {theta})) x) := by
      rw [hphase theta htheta]
      exact fun y => (hphases theta htheta y).1
    exact ⟨hi x, hamiltonZeroPhaseMap_pi1_injective psi Fpsi theta x (hi x)⟩
  · rw [hA, hB]
    exact ⟨Nlower, Nupper, lower, upper, hcount, hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩
  · intro theta htheta
    have htheta' : (theta : C0) ∈ ({(a : C0), (b : C0)} : Set C0) := by
      rcases htheta with rfl | rfl <;> simp
    rw [hphase theta htheta']
    exact hproducts theta htheta

end PoincareConjecture.M76
