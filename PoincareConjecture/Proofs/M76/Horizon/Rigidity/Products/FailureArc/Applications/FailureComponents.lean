import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Applications.RetainedProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.OriginalFailureComponents








set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem exists_hamiltonZero_rigidity_or_original_failure_component_products
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    (∃ f : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 f) ∧
      Nonempty (phi.HomotopyRel ⟨f, f.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨f, f.continuous⟩ B0)) ∨
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      ∃ (R : Set X0) (a b : C0), a ≠ b ∧ IsCompact R ∧ IsPLIrreducible e R ∧
        IsCoveringMap (hamiltonZeroRetainedTangentialMap psi (frontier R)) ∧
        HamiltonZeroBoundaryFailureArc e R psi ∧
        ∀ x ∈ R, let P := connectedComponentIn R x
          IsCompact P ∧ IsConnected P ∧ IsPLIrreducible e P ∧
          (∀ z : P, (z : X0) ∈ frontier R ↔ (z : X0) ∈ frontier P) ∧
          ∃ (S₀ S₁ : Set X0) (hS₀ : S₀ ⊆ P) (hS₁ : S₁ ⊆ P)
            (x₀ : S₀) (x₁ : S₁),
            S₀ ⊆ frontier P ∧ S₁ ⊆ frontier P ∧ Disjoint S₀ S₁ ∧
            connectedComponentIn (frontier P) (x₀ : X0) = S₀ ∧
            connectedComponentIn (frontier P) (x₁ : X0) = S₁ ∧
            (∀ z : S₀, Nontrivial (FundamentalGroup S₀ z)) ∧
            (∀ z : S₁, Nontrivial (FundamentalGroup S₁ z)) ∧
            (∀ z : S₀, Function.Injective (FundamentalGroup.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(S₀, X0)) z)) ∧
            (∀ z : S₁, Function.Injective (FundamentalGroup.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(S₁, X0)) z)) ∧
            (∀ z ∈ S₀, hamiltonZeroCircleMap psi z = a) ∧
            (∀ z ∈ S₁, hamiltonZeroCircleMap psi z = b) ∧
            (∃ (A B : OriginalTorusEulerCandidate e P (frontier P)),
              A.surface = S₀ ∧ B.surface = S₁) ∧
            ∃ k : Path ((ContinuousMap.inclusion hS₀) x₀) ((ContinuousMap.inclusion hS₁) x₁),
              (FundamentalGroup.map (ContinuousMap.inclusion hS₀) x₀).range.Commensurable
                (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
                  (FundamentalGroup.map (ContinuousMap.inclusion hS₁) x₁)).range) ∧
              ∃ H : (S₀ × unitInterval) ≃ₜ P,
                (∀ z, (H (z, ⟨0, by norm_num⟩) : X0) = z) ∧
                range (fun z => (H (z, ⟨1, by norm_num⟩) : X0)) = S₁ ∧
                (∀ z t, (H (z, t) : X0) ∈ frontier P ↔
                  (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
                ∃ (s : Finset P) (G : X0 → (s → ℝ × V3))
                  (HG : ((G '' S₀) ×ˢ Set.Icc (0 : ℝ) 1) ≃ₜ (G '' P)),
                  Continuous G ∧
                  (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
                  (∀ z ∈ P, ∀ y : X0, G z = G y → z = y) ∧
                  HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
                  (∀ (z : S₀) (t : unitInterval),
                    (HG ⟨(G z, t), ⟨mem_image_of_mem G z.property, t.property⟩⟩ :
                      s → ℝ × V3) = G (H (z, t))) ∧
                  ∀ z ∈ P, ∃ (i : ι) (V : Set X0) (c : (s → ℝ × V3) →ᴬ[ℝ] V3),
                    IsOpen V ∧ z ∈ V ∧ V ⊆ (e i).source ∧ EqOn (c ∘ G) (e i) V := by
  rcases exists_hamiltonZero_rigidity_or_original_failure_components e d hI hd phi hphi F
    with hrigid | hfailure
  · exact Or.inl hrigid
  obtain ⟨psi, hpsi, hphipsi, hidpsi, R, a, b, hab, hR, hIR, hcover, harc, hcomponents⟩ :=
    hfailure
  refine Or.inr ⟨psi, hpsi, hphipsi, hidpsi, R, a, b, hab, hR, hIR, hcover, harc, ?_⟩
  intro x hx P
  obtain ⟨hP, hconn, hIP, hfront, S₀, S₁, hS₀, hS₁, x₀, x₁,
    hS₀front, hS₁front, hdis, hcomponent₀, hcomponent₁,
    hnt₀, hnt₁, hinj₀, hinj₁, hphase₀, hphase₁, hcandidates, k, hcomm⟩ := hcomponents x hx
  refine ⟨hP, hconn, hIP, hfront, S₀, S₁, hS₀, hS₁, x₀, x₁,
    hS₀front, hS₁front, hdis, hcomponent₀, hcomponent₁,
    hnt₀, hnt₁, hinj₀, hinj₁, hphase₀, hphase₁, hcandidates, k, hcomm, ?_⟩
  exact exists_original_marked_product_of_retained_component hIP hP hconn
    hS₀front hS₁front hdis x₀ x₁ hcomponent₀ hcomponent₁
    (hnt₀ x₀) (hnt₁ x₁) (hinj₀ x₀) (hinj₁ x₁) k hcomm

end PoincareConjecture.M76
