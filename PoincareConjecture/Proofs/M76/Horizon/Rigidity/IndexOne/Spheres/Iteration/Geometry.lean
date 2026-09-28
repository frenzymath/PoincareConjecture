import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Frontier.AmbientPhases

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

structure PairedSourceGeometry {α : Type*}
    (e : α → OpenPartialHomeomorph X V3) (phi : C(H, H)) (a b : ℝ) : Prop where
  domains : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
    PLDomain e (sourceSlab phi uv.1 uv.2)
  frontiers : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
    frontier (sourceSlab phi uv.1 uv.2) =
      (sourceSlab phi uv.1 uv.2 ∩ frontier R) ∪
        (sourceSurface phi (uv.1 : C) ∪ sourceSurface phi (uv.2 : C))
  corners : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
    ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
      ∀ x ∈ sourceSurface phi (theta : C) ∩ frontier R,
        ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3)
            (G : OpenPartialHomeomorph X V3),
          psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
          x ∈ G.source ∧ psi (G x) = 0 ∧
          (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ↔ 0 ≤ psi (G y)) ∧
          (∀ y ∈ G.source, y ∈ sourceSlab phi uv.1 uv.2 ∩ frontier R ↔
            psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
          ∀ y ∈ G.source, y ∈ sourceSurface phi (theta : C) ↔
            psi (G y) = 0 ∧ lambda (G y) ≤ 0
  ambient_injective : ∀ theta ∈ ({a, b} : Set ℝ),
    ∀ x : sourceSurface phi (theta : C), Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi (theta : C), X)) x)

theorem exists_relative_paired_source_geometry
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
        eta ⁻¹' B = phi ⁻¹' B ∧ PairedSourceGeometry e eta a b := by
  obtain ⟨a, ha, b, hb, eta, K, hK, hKR, hfixed, heta, Heta, Feta, hB, hinj, hslabs⟩ :=
    exists_complementary_sourcePhases_ambient_pi1_injective e d hd phi hphi F0
  refine ⟨a, ha, b, hb, eta, K, hK, hKR, hfixed, heta, Heta, Feta, hB, ?_⟩
  exact {
    domains := fun uv huv => (hslabs uv huv).2.choose
    frontiers := fun uv huv => (hslabs uv huv).2.choose_spec.1
    corners := fun uv huv theta htheta => ((hslabs uv huv).2.choose_spec.2 theta htheta).2
    ambient_injective := hinj }

end PoincareConjecture.M76.HamiltonIntervalTorus
