import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleSlab
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryProduct

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

open Classical in

theorem exists_hamiltonZero_regular_slab_product {ι κ : Type*}
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
        IsCompact (q ⁻¹' {(a : C0)}) ∧ (q ⁻¹' {(a : C0)}).Nonempty ∧
        IsCompact (q ⁻¹' {(b : C0)}) ∧ (q ⁻¹' {(b : C0)}).Nonempty ∧
        Disjoint (q ⁻¹' {(a : C0)}) (q ⁻¹' {(b : C0)}) ∧
        IsCompact R ∧ PLDomain e R ∧ frontier R = S ∧
        IsCompact (interior R)ᶜ ∧ PLDomain e (interior R)ᶜ ∧
        frontier (interior R)ᶜ = S ∧
        (interior R).Nonempty ∧ (interior (interior R)ᶜ).Nonempty ∧
        (∀ c ∈ ({(a : C0), (b : C0)} : Set C0), ∀ x : X0, q x = c →
          ∃ (d0 : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
            (G : OpenPartialHomeomorph X0 V3),
            (d0 : C0) = c ∧ ell.contLinear v = 1 ∧
            x ∈ G.source ∧ ell (G x) = 0 ∧
            (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ G.source, q y = ((ell (G y) + d0 : ℝ) : C0)) ∧
            ∀ y ∈ G.source, q y = c ↔ ell (G y) = 0) ∧
        ∀ U : Set X0, IsOpen U → S ⊆ U →
          ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
            (HB : L.space ≃ₜ frontier R) (C : (s → ℝ × V3) × ℝ → X0),
            L.faces.Finite ∧
            PolyhedralPLInCharts e C (L.space ×ˢ Icc (-1 : ℝ) 1) ∧
            Topology.IsEmbedding
              (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)) => C z) ∧
            (∀ x : L.space, C ((x : s → ℝ × V3), 0) = HB x) ∧
            (∀ z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)),
              (C z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
              (C z ∈ R ↔ 0 ≤ (z : (s → ℝ × V3) × ℝ).2) ∧
              (C z ∈ (interior R)ᶜ ↔ (z : (s → ℝ × V3) × ℝ).2 ≤ 0)) ∧
            ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
              MapsTo C (L.space ×ˢ Icc (-delta) delta) U ∧
              ∀ eps : ℝ, 0 < eps → eps ≤ delta →
                IsOpen (C '' (L.space ×ˢ Ioo (-eps) eps)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular⟩ := exists_hamiltonZero_regular_circle_slab e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular, ?_⟩
  intro U hU hSU
  exact he.exists_small_boundary_product_of_interiors_nonempty hR hminus hne hneminus hU
    (hfront.subset.trans hSU)

end PoincareConjecture.M76
