import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedSlabProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SupportedCollarCollapse

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

theorem exists_hamiltonZero_slab_source_collapse {ι κ : Type*}
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
            (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X0),
            L.faces.Finite ∧
            PolyhedralPLInCharts e c (L.space ×ˢ Icc (-1 : ℝ) 1) ∧
            Topology.IsEmbedding
              (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
            (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
            (∀ z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)),
              (c z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
              (c z ∈ R ↔ 0 ≤ (z : (s → ℝ × V3) × ℝ).2) ∧
              (c z ∈ (interior R)ᶜ ↔ (z : (s → ℝ × V3) × ℝ).2 ≤ 0)) ∧
            ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
              MapsTo c (L.space ×ˢ Icc (-delta) delta) U ∧
              (∀ eps : ℝ, 0 < eps → eps ≤ delta →
                IsOpen (c '' (L.space ×ˢ Ioo (-eps) eps))) ∧
              ∀ r : ℝ, 0 < r → 2 * r < delta →
                ∃ D : C(unitInterval × X0, X0),
                  (∀ y : X0, D (0, y) = y) ∧
                  (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                    z ∈ L.space ×ˢ Icc (-delta) delta →
                    D (t, c z) = c (z.1, CollarCollapse.move r t z.2)) ∧
                  (∀ (t : unitInterval) (y : X0),
                    y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → D (t, y) = y) ∧
                  (∀ (t : unitInterval) (y : X0), y ∈ S → D (t, y) = y) ∧
                  (∀ (t : unitInterval) (y : X0), y ∉ U → D (t, y) = y) ∧
                  (∀ (t : unitInterval) (x : s → ℝ × V3), x ∈ L.space →
                    D (t, c (x, 0)) = c (x, 0)) ∧
                  (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                    z ∈ L.space ×ˢ ({-delta, delta} : Set ℝ) → D (t, c z) = c z) ∧
                  ∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                    D (1, c z) = c (z.1, 0) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular, hproduct⟩ :=
    exists_hamiltonZero_regular_slab_product e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular, ?_⟩
  intro U hU hSU
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hopen⟩ := hproduct U hU hSU
  refine ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hopen, ?_⟩
  intro r hr hwidth
  have hdeltaOne : delta ≤ 1 := by linarith
  have hsub : L.space ×ˢ Icc (-delta) delta ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, (neg_le_neg hdeltaOne).trans hz.2.1, hz.2.2.trans hdeltaOne⟩
  have hsmall : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-delta) delta : Set ((s → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hsub)
  obtain ⟨D, hDzero, hDvalue, hDfixed, hDbase, hDends, hDinner⟩ :=
    CollarCollapse.exists_supported_source_family (L.isCompact_space_of_finite hL)
      hr hwidth c (hc.continuousOn.mono hsub) hsmall (hopen delta hdelta le_rfl)
  refine ⟨D, hDzero, hDvalue, hDfixed, ?_, ?_, hDbase, hDends, hDinner⟩
  · intro t y hy
    have hyfront := hfront.symm.subset hy
    let x : L.space := HB.symm ⟨y, hyfront⟩
    have hcy : c ((x : s → ℝ × V3), 0) = y :=
      (hbase x).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨y, hyfront⟩))
    rw [← hcy]
    exact hDbase t x x.property
  · intro t y hy
    apply hDfixed t y
    rintro ⟨z, hz, hzy⟩
    apply hy
    rw [← hzy]
    exact hcU ⟨hz.1, (neg_le_neg hwidth.le).trans hz.2.1.le,
      hz.2.2.le.trans hwidth.le⟩

end PoincareConjecture.M76
