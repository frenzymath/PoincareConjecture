import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedSlabEndpointPL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteCollarPhaseProducts











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







theorem exists_hamiltonZero_adjusted_phase_products {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ a ∈ Ioo ((4 * 16 : ℝ) / 4) ((4 * 16 : ℝ) / 3),
      ∃ b ∈ Ioo (2 * (4 * 16 : ℝ) / 3) (3 * (4 * 16 : ℝ) / 4),
        0 < a ∧ a < b ∧ b < 4 * 16 ∧
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
        (∀ c ∈ ({(a : C0), (b : C0)} : Set C0), ∀ x : X0, q x = c →
          ∃ (d0 : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v0 : V3)
            (H : OpenPartialHomeomorph X0 V3),
            (d0 : C0) = c ∧ ell.contLinear v0 = 1 ∧
            x ∈ H.source ∧ ell (H x) = 0 ∧
            (∀ j, (e j).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ H.source, q y = ((ell (H y) + d0 : ℝ) : C0)) ∧
            ∀ y ∈ H.source, q y = c ↔ ell (H y) = 0) ∧
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
                      PolyhedralPLInCharts d (fun z => G (1, c z))
                        (L.space ×ˢ Icc (-delta) delta) ∧
                      ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain
                        ⟨fun y => G (1, y),
                          G.continuous.comp (continuous_const.prodMk continuous_id)⟩) ∧
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
                            Icc (-rho) rho) ∧
                        ∀ t ∈ ({a, b} : Set ℝ),
                          ∃ (J : SimplicialComplex ℝ (s → ℝ × V3))
                            (H : J.space ≃ₜ (q ⁻¹' {(t : C0)} : Set X0))
                            (K : SimplicialComplex ℝ ((s → ℝ × V3) × ℝ)),
                            J.faces.Finite ∧ J ≤ L ∧
                            J.space = {x | x ∈ L.space ∧ q (c (x, 0)) = (t : C0)} ∧
                            (∀ x : J.space, (H x : X0) = c ((x : s → ℝ × V3), 0)) ∧
                            PolyhedralPLInCharts e (fun x => c (x, 0)) J.space ∧
                            K.faces.Finite ∧ K.space = J.space ×ˢ Icc (-rho) rho ∧
                            PolyhedralPLInCharts e c K.space ∧
                            Topology.IsEmbedding (fun z : K.space => c z) ∧
                            (∀ eps : ℝ, 0 < eps → eps ≤ delta →
                              IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps))) ∧
                            (fun y => (Q (G (1, y))).2) ⁻¹'
                                AddCircle.closedIntervalArc (4 * 16) (t - rho) (t + rho) =
                              c '' K.space := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular, eta, heta, haeta, habeta, hbeta, hfamily⟩ :=
    exists_hamiltonZero_adjusted_map_PL e d hd phi hphi F
  refine ⟨a, haI, b, hbI, ha, hab, hb, hSa, hna, hSb, hnb,
    hdisjoint, hR, he, hfront, hminus, heminus, hfrontminus,
    hne, hneminus, hregular, eta, heta, haeta, habeta, hbeta, ?_⟩
  intro U0 hU0 hSU0
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hcA, hopen,
    v, hvc, hval, hperiod, hlabels, hsigns,
    r, hr, hwidth, hrEta, D, w, G,
    hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, hwvalue, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, hGzero, hGS, hGout, hGfixed, hGinner, hlevels, hparameter, hendpoint,
    rho, hrho, hrhor, hpre, hpreA, hpreB⟩ := hfamily U0 hU0 hSU0
  refine ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hcA, hopen,
    v, hvc, hval, hperiod, hlabels, hsigns,
    r, hr, hwidth, hrEta, D, w, G,
    hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, hwvalue, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, hGzero, hGS, hGout, hGfixed, hGinner, hlevels, hparameter, hendpoint,
    rho, hrho, hrhor, hpre, hpreA, hpreB, ?_⟩
  intro t ht
  have htLabel : (t : C0) ∈ ({(a : C0), (b : C0)} : Set C0) := by
    rcases ht with rfl | rfl <;> simp
  obtain ⟨J, H, hJ, hJL, hJs, hH, hzero, hproducts, hJopen⟩ :=
    L.exists_finite_collar_phase_products hL HB (hamiltonZeroCircleMap phi)
      ((finite_singleton (b : C0)).insert (a : C0)) hfront hc hi hbase
      (show delta ≤ 1 by linarith) hopen htLabel
  obtain ⟨K, hK, hKs, hcK, hiK⟩ := hproducts rho hrho (show rho ≤ delta by linarith)
  refine ⟨J, H, K, hJ, hJL, hJs, hH, hzero, hK, hKs, hcK, hiK, hJopen, ?_⟩
  rw [hKs, hJs]
  rcases ht with rfl | rfl
  · exact hpreA
  · exact hpreB

end PoincareConjecture.M76
