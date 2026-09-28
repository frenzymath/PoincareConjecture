import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.LevelPreimages
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCircleAvoidance
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SignedPhaseArcMembership









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

theorem exists_hamiltonZero_adjusted_neighborhood {ι κ : Type*}
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
        ∃ eta : ℝ, 0 < eta ∧ 0 < a - 2 * eta ∧
          a + 2 * eta < b - 2 * eta ∧ b + 2 * eta < 4 * 16 ∧
          ∀ U0 : Set X0, IsOpen U0 → S ⊆ U0 →
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
                MapsTo c (L.space ×ˢ Icc (-delta) delta) U0 ∧
                MapsTo (fun z => q (c z)) (L.space ×ˢ Icc (-delta) delta)
                  (AddCircle.openIntervalArc (4 * 16) (a - eta) (a + eta) ∪
                    AddCircle.openIntervalArc (4 * 16) (b - eta) (b + eta)) ∧
                (∀ eps : ℝ, 0 < eps → eps ≤ delta →
                  IsOpen (c '' (L.space ×ˢ Ioo (-eps) eps))) ∧
                ∃ v : (s → ℝ × V3) × ℝ → ℝ,
                  ContinuousOn v (L.space ×ˢ Icc (-delta) delta) ∧
                  (∀ z ∈ L.space ×ˢ Icc (-delta) delta, (v z : C0) = q (c z)) ∧
                  (∀ z ∈ L.space ×ˢ Icc (-delta) delta, v z ∈ Ioo (0 : ℝ) (4 * 16)) ∧
                  (∀ x ∈ L.space, q (c (x, 0)) ∈ ({(a : C0), (b : C0)} : Set C0)) ∧
                  (∀ x ∈ L.space,
                    (q (c (x, 0)) = (a : C0) → ∀ t ∈ Icc (-delta) delta,
                      |v (x, t) - a| < eta ∧ (v (x, t) = a ↔ t = 0) ∧
                      (a ≤ v (x, t) ↔ 0 ≤ t) ∧ (a < v (x, t) ↔ 0 < t) ∧
                      (v (x, t) < a ↔ t < 0)) ∧
                    (q (c (x, 0)) = (b : C0) → ∀ t ∈ Icc (-delta) delta,
                      |v (x, t) - b| < eta ∧ (v (x, t) = b ↔ t = 0) ∧
                      (v (x, t) ≤ b ↔ 0 ≤ t) ∧ (v (x, t) < b ↔ 0 < t) ∧
                      (b < v (x, t) ↔ t < 0))) ∧
                  ∃ r : ℝ, 0 < r ∧ 2 * r < delta ∧ r < eta / 4 ∧
                    ∃ (D : C(unitInterval × X0, X0)) (w : C(unitInterval × X0, ℝ))
                      (G : C(unitInterval × X0, X0)),
                      (∀ y : X0, D (0, y) = y) ∧
                      (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                        z ∈ L.space ×ˢ Icc (-delta) delta →
                        D (t, c z) = c (z.1, CollarCollapse.move r t z.2)) ∧
                      (∀ (t : unitInterval) (y : X0),
                        y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → D (t, y) = y) ∧
                      (∀ (t : unitInterval) (y : X0), y ∈ S → D (t, y) = y) ∧
                      (∀ (t : unitInterval) (y : X0), y ∉ U0 → D (t, y) = y) ∧
                      (∀ (t : unitInterval) (x : s → ℝ × V3), x ∈ L.space →
                        D (t, c (x, 0)) = c (x, 0)) ∧
                      (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                        z ∈ L.space ×ˢ ({-delta, delta} : Set ℝ) → D (t, c z) = c z) ∧
                      (∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                        D (1, c z) = c (z.1, 0)) ∧
                      (∀ y : X0, w (0, y) = 0) ∧
                      (∀ (t : unitInterval) (z : (s → ℝ × V3) × ℝ),
                        z ∈ L.space ×ˢ Icc (-delta) delta →
                        w (t, c z) = (t : ℝ) *
                          (if q (c (z.1, 0)) = (a : C0) then 1 else -1) *
                            CollarCollapse.displacement r z.2) ∧
                      (∀ (t : unitInterval) (y : X0),
                        y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → w (t, y) = 0) ∧
                      (∀ (t : unitInterval) (y : X0), y ∈ S → w (t, y) = 0) ∧
                      (∀ (t : unitInterval) (y : X0), y ∉ U0 → w (t, y) = 0) ∧
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
                      (∀ (t : unitInterval) (y : X0), y ∉ U0 → G (t, y) = f y) ∧
                      (∀ (t : unitInterval) (y : X0),
                        y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → G (t, y) = f y) ∧
                      (∀ z : (s → ℝ × V3) × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
                        Q (G (1, c z)) = ((Q (f (c (z.1, 0)))).1,
                          q (c (z.1, 0)) +
                            (((if q (c (z.1, 0)) = (a : C0) then 1 else -1) * z.2 : ℝ) : C0))) ∧
                      (∀ t : unitInterval,
                        (fun y => (Q (G (t, y))).2) ⁻¹' {(a : C0)} = q ⁻¹' {(a : C0)} ∧
                        (fun y => (Q (G (t, y))).2) ⁻¹' {(b : C0)} = q ⁻¹' {(b : C0)}) ∧
                      ∃ rho : ℝ, 0 < rho ∧ rho < r ∧
                        (fun y => (Q (G (1, y))).2) ⁻¹'
                          (AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) ∪
                            AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho)) ⊆
                          c '' (L.space ×ˢ Ioo (-r) r) ∧
                        (fun y => (Q (G (1, y))).2) ⁻¹'
                            AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) =
                          c '' ({x : s → ℝ × V3 | x ∈ L.space ∧ q (c (x, 0)) = (a : C0)} ×ˢ
                            Icc (-rho) rho) ∧
                        (fun y => (Q (G (1, y))).2) ⁻¹'
                            AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho) =
                          c '' ({x : s → ℝ × V3 | x ∈ L.space ∧ q (c (x, 0)) = (b : C0)} ×ˢ
                            Icc (-rho) rho) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  let q := hamiltonZeroCircleMap phi
  obtain ⟨hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, eta, heta, haeta, habeta, hbeta, hfamily⟩ :=
    exists_hamiltonZero_level_preserving_adjustment e d hd phi hphi F a b ha hab hb he0 hfront0
  refine ⟨hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, eta, heta, haeta, habeta, hbeta, ?_⟩
  intro U0 hU0 hSU0
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hcA, hopen,
    v, hvc, hval, hperiod, hlabels, hsigns,
    r, hr, hwidth, hrEta, D, w, G,
    hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, hwvalue, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, hGzero, hGS, hGout, hGfixed, hGinner, hlevels⟩ := hfamily U0 hU0 hSU0
  let W := c '' (L.space ×ˢ Ioo (-r) r)
  have hW : IsOpen W := hopen r hr (by linarith)
  have hSW : q ⁻¹' ({(a : C0), (b : C0)} : Set C0) ⊆ W := by
    intro y hy
    have hyfront : y ∈ frontier (q ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) := by
      rw [hfront]
      exact hy
    obtain ⟨x, hxy⟩ := HB.surjective ⟨y, hyfront⟩
    refine ⟨((x : s → ℝ × V3), 0), ⟨x.property, ?_⟩, ?_⟩
    · constructor <;> linarith
    · exact (hbase x).trans (congrArg Subtype.val hxy)
  let n : C(X0, C0) := ⟨fun y => (Q (G (1, y))).2,
    continuous_snd.comp (Q.continuous.comp
      (G.continuous.comp (continuous_const.prodMk continuous_id)))⟩
  let K := n '' Wᶜ
  have hK : IsCompact K := hW.isClosed_compl.isCompact.image n.continuous
  have hKa : (a : C0) ∉ K := by
    rintro ⟨y, hy, hny⟩
    have hyLevel : y ∈ (fun y => (Q (G (1, y))).2) ⁻¹' {(a : C0)} := hny
    rw [(hlevels 1).1] at hyLevel
    exact hy (hSW (Or.inl hyLevel))
  have hKb : (b : C0) ∉ K := by
    rintro ⟨y, hy, hny⟩
    have hyLevel : y ∈ (fun y => (Q (G (1, y))).2) ⁻¹' {(b : C0)} := hny
    rw [(hlevels 1).2] at hyLevel
    exact hy (hSW (Or.inr hyLevel))
  obtain ⟨rho, hrho, hrhor, havoidA, havoidB⟩ :=
    AddCircle.exists_closed_phase_arcs_disjoint (4 * (16 : ℝ)) hK hKa hKb hr
  have hpre : n ⁻¹'
      (AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) ∪
        AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho)) ⊆ W := by
    intro y hy
    by_contra hyW
    have hny : n y ∈ K := ⟨y, hyW, rfl⟩
    rcases hy with hy | hy
    · exact disjoint_left.mp havoidA hny hy
    · exact disjoint_left.mp havoidB hny hy
  have hninner (z : (s → ℝ × V3) × ℝ) (hz : z ∈ L.space ×ˢ Icc (-r) r) :
      n (c z) = q (c (z.1, 0)) +
        (((if q (c (z.1, 0)) = (a : C0) then 1 else -1) * z.2 : ℝ) : C0) := by
    exact congrArg (fun z : (C0 × C0) × C0 => z.2) (hGinner z hz)
  have htests (z : (s → ℝ × V3) × ℝ) (hz : z ∈ L.space ×ˢ Icc (-r) r) :
      (n (c z) ∈ AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) ↔
        q (c (z.1, 0)) = (a : C0) ∧ z.2 ∈ Icc (-rho) rho) ∧
      (n (c z) ∈ AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho) ↔
        q (c (z.1, 0)) = (b : C0) ∧ z.2 ∈ Icc (-rho) rho) := by
    rw [hninner z hz]
    exact AddCircle.signed_phase_arc_membership (4 * (16 : ℝ)) hr.le
      (by linarith) (by linarith) (by linarith) hrhor.le hz.2 (hlabels z.1 hz.1)
  have hpreA : n ⁻¹' AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) =
      c '' ({x : s → ℝ × V3 | x ∈ L.space ∧ q (c (x, 0)) = (a : C0)} ×ˢ
        Icc (-rho) rho) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := hpre (Or.inl hy)
      have hzInner : z ∈ L.space ×ˢ Icc (-r) r := ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
      have hzArc : n (c z) ∈ AddCircle.closedIntervalArc (4 * 16) (a - rho) (a + rho) := by
        rw [hzy]
        exact hy
      obtain ⟨hphase, htime⟩ := (htests z hzInner).1.mp hzArc
      exact ⟨z, ⟨⟨hz.1, hphase⟩, htime⟩, hzy⟩
    · rintro ⟨z, hz, rfl⟩
      have hzInner : z ∈ L.space ×ˢ Icc (-r) r :=
        ⟨hz.1.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact (htests z hzInner).1.mpr ⟨hz.1.2, hz.2⟩
  have hpreB : n ⁻¹' AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho) =
      c '' ({x : s → ℝ × V3 | x ∈ L.space ∧ q (c (x, 0)) = (b : C0)} ×ˢ
        Icc (-rho) rho) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := hpre (Or.inr hy)
      have hzInner : z ∈ L.space ×ˢ Icc (-r) r := ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
      have hzArc : n (c z) ∈ AddCircle.closedIntervalArc (4 * 16) (b - rho) (b + rho) := by
        rw [hzy]
        exact hy
      obtain ⟨hphase, htime⟩ := (htests z hzInner).2.mp hzArc
      exact ⟨z, ⟨⟨hz.1, hphase⟩, htime⟩, hzy⟩
    · rintro ⟨z, hz, rfl⟩
      have hzInner : z ∈ L.space ×ˢ Icc (-r) r :=
        ⟨hz.1.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      exact (htests z hzInner).2.mpr ⟨hz.1.2, hz.2⟩
  exact ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hcA, hopen,
    v, hvc, hval, hperiod, hlabels, hsigns,
    r, hr, hwidth, hrEta, D, w, G,
    hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, hwvalue, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, hGzero, hGS, hGout, hGfixed, hGinner, hlevels,
    rho, hrho, hrhor, hpre, hpreA, hpreB⟩

end PoincareConjecture.M76.PrescribedSlab

