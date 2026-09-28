import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.SourceCollapse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SupportedCollarDisplacement
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslation

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.PrescribedSlab

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

open Classical in

theorem exists_hamiltonZero_slab_adjustment {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 4 * 16)
    (he0 : PLDomain e ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront0 : frontier ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b) =
      (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0), (b : C0)}) :
        let f := hamiltonZeroAmbientMap phi
        let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
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
                ∃ (D : C(unitInterval × X0, X0)) (w : C(unitInterval × X0, ℝ))
                  (G : C(unitInterval × X0, X0)),
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
                  (∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                    D (1, c z) = c (z.1, 0)) ∧
                  (∀ y : X0, w (0, y) = 0) ∧
                  (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                    z ∈ L.space ×ˢ Icc (-delta) delta →
                    w (t, c z) = (t : ℝ) * (if q (c (z.1, 0)) = (a : C0) then 1 else -1) *
                      CollarCollapse.displacement r z.2) ∧
                  (∀ (t : unitInterval) (y : X0),
                    y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → w (t, y) = 0) ∧
                  (∀ (t : unitInterval) (y : X0), y ∈ S → w (t, y) = 0) ∧
                  (∀ (t : unitInterval) (y : X0), y ∉ U → w (t, y) = 0) ∧
                  (∀ (t : unitInterval) (x : s → ℝ × V3), x ∈ L.space →
                    w (t, c (x, 0)) = 0) ∧
                  (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                    z ∈ L.space ×ˢ ({-delta, delta} : Set ℝ) → w (t, c z) = 0) ∧
                  (∀ (t : unitInterval) (y : X0), |w (t, y)| ≤ r) ∧
                  (∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                    (q (c (z.1, 0)) = (a : C0) → w (1, c z) = z.2) ∧
                    (q (c (z.1, 0)) = (b : C0) → w (1, c z) = -z.2)) ∧
                  (∀ (t : unitInterval) (y : X0),
                    G (t, y) = hamiltonZeroTargetTranslation (w (t, y), f (D (t, y)))) ∧
                  (∀ y : X0, G (0, y) = f y) ∧
                  (∀ (t : unitInterval) (y : X0), y ∈ S → G (t, y) = f y) ∧
                  (∀ (t : unitInterval) (y : X0), y ∉ U → G (t, y) = f y) ∧
                  (∀ (t : unitInterval) (y : X0),
                    y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → G (t, y) = f y) ∧
                  ∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                    Q (G (1, c z)) = ((Q (f (c (z.1, 0)))).1,
                      q (c (z.1, 0)) +
                        (((if q (c (z.1, 0)) = (a : C0) then 1 else -1) * z.2 : ℝ) : C0)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let f := hamiltonZeroAmbientMap phi
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  let q := hamiltonZeroCircleMap phi
  obtain ⟨hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hfamily⟩ :=
    exists_hamiltonZero_slab_source_collapse e d hd phi hphi F a b ha hab hb he0 hfront0
  have habq : (a : C0) ≠ (b : C0) := by
    intro heq
    obtain ⟨y, hy⟩ := hna
    have hya : q y = (a : C0) := hy
    have hyb : y ∈ q ⁻¹' {(b : C0)} := hya.trans heq
    exact disjoint_left.mp hdisjoint hy hyb
  refine ⟨hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, ?_⟩
  intro U hU hSU
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hopen, hsource⟩ := hfamily U hU hSU
  refine ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hopen, ?_⟩
  intro r hr hwidth
  obtain ⟨D, hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner⟩ :=
    hsource r hr hwidth
  have hdeltaOne : delta ≤ 1 := by linarith
  have hsub : L.space ×ˢ Icc (-delta) delta ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, (neg_le_neg hdeltaOne).trans hz.2.1, hz.2.2.trans hdeltaOne⟩
  have hsmall : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-delta) delta : Set ((s → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hsub)
  have hphase : ∀ x ∈ L.space, q (c (x, 0)) ∈ ({(a : C0), (b : C0)} : Set C0) := by
    intro x hx
    have hzero : c (x, 0) = (HB ⟨x, hx⟩ : X0) := hbase ⟨x, hx⟩
    rw [hzero]
    exact hfront.subset (HB ⟨x, hx⟩).property
  obtain ⟨w, hwzero, hwvalue, hwfixed, hwbase, hwends, hwbound, hwinner⟩ :=
    CollarCollapse.exists_supported_displacement L hL hr hwidth c
      (hc.continuousOn.mono hsub) hsmall (hopen delta hdelta le_rfl)
      q (a : C0) (b : C0) habq hphase
  have hwS (t : unitInterval) (y : X0)
      (hy : y ∈ q ⁻¹' {(a : C0), (b : C0)}) : w (t, y) = 0 := by
    have hyfront := hfront.symm.subset hy
    let x : L.space := HB.symm ⟨y, hyfront⟩
    have hcy : c ((x : s → ℝ × V3), 0) = y :=
      (hbase x).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨y, hyfront⟩))
    rw [← hcy]
    exact hwbase t x x.property
  have hwout (t : unitInterval) (y : X0) (hy : y ∉ U) : w (t, y) = 0 := by
    apply hwfixed t y
    rintro ⟨z, hz, hzy⟩
    apply hy
    rw [← hzy]
    exact hcU ⟨hz.1, (neg_le_neg hwidth.le).trans hz.2.1.le,
      hz.2.2.le.trans hwidth.le⟩
  let G : C(unitInterval × X0, X0) :=
    ⟨fun z => hamiltonZeroTargetTranslation (w z, f (D z)),
      hamiltonZeroTargetTranslation.continuous.comp
        (w.continuous.prodMk (f.continuous.comp D.continuous))⟩
  have hGvalue (t : unitInterval) (y : X0) :
      G (t, y) = hamiltonZeroTargetTranslation (w (t, y), f (D (t, y))) := rfl
  refine ⟨D, w, G, hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, ?_, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, ?_, ?_, ?_, ?_, ?_⟩
  · intro t z hz
    by_cases hqa : hamiltonZeroCircleMap phi (c (z.1, 0)) = (a : C0)
    · simpa only [q, if_pos hqa] using hwvalue t z hz
    · simpa only [q, if_neg hqa] using hwvalue t z hz
  · intro y
    rw [hGvalue, hwzero, hDzero, hamiltonZeroTargetTranslation_zero]
  · intro t y hy
    rw [hGvalue, hwS t y hy, hDS t y hy, hamiltonZeroTargetTranslation_zero]
  · intro t y hy
    rw [hGvalue, hwout t y hy, hDout t y hy, hamiltonZeroTargetTranslation_zero]
  · intro t y hy
    rw [hGvalue, hwfixed t y hy, hDfixed t y hy, hamiltonZeroTargetTranslation_zero]
  · intro z hz
    have hw : w (1, c z) =
        (if q (c (z.1, 0)) = (a : C0) then 1 else -1) * z.2 := by
      by_cases hqa : q (c (z.1, 0)) = (a : C0)
      · simpa [hqa] using (hwinner z hz).1 hqa
      · have hqb : q (c (z.1, 0)) = (b : C0) := by
          rcases hphase z.1 hz.1 with h | h
          · exact (hqa h).elim
          · exact h
        simpa [hqa] using (hwinner z hz).2 hqb
    have hnormal : (Q (f (c (z.1, 0)))).2 = q (c (z.1, 0)) :=
      hamiltonZeroAmbientMap_circle phi (c (z.1, 0))
    rw [hGvalue, hDinner z hz, hamiltonZeroTargetTranslation_coordinates, hw, hnormal]

end PoincareConjecture.M76.PrescribedSlab
