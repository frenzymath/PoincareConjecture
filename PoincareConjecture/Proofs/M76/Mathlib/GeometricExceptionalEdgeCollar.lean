import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleTaperedCollar
import PoincareConjecture.Proofs.M76.Mathlib.TaperedSourceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.RegularSlabTriangleLabels










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]







theorem exists_exceptional_triangle_geometric_edge_collar_with_formula
    (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hi : AffineIndependent ℝ ![q, u, v]) (hq : A q = 0)
    (hu : A u < 0) (hv : 0 < A v) {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    ∃ G : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ≃ₜ
        convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)),
      G.IsFinitePL ∧
        (∀ p, (G p : E) = (p : E × ℝ).1 +
          (p : E × ℝ).2 • A.heightRay (A.zeroCrossing u v) v) ∧
        (∀ p, A (G p) = (p : E × ℝ).2) ∧
        (∀ p : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β,
          (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
        (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ⊆
          convexHull ℝ (insert q ({u, v} : Set E))) ∧
        (convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} =
          segment ℝ q (A.zeroCrossing u v)) ∧
        ∀ e : Finset E, e.card = 2 → e ⊆ {q, u, v} →
          ∀ p : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β,
            (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
              (G p : E) ∈ convexHull ℝ (e : Set E) := by
  obtain ⟨H, hH, hval, hheight, hsub, hsection, hside, hneg, hfar⟩ :=
    A.exists_exceptional_triangle_tapered_collar hi hq hu hv hβ hβv
  let w := A.zeroCrossing u v
  have hqw : q ≠ w := by
    intro h
    let p0 : TaperedStrip.domain β := ⟨(0, 0), by simp [TaperedStrip.domain]⟩
    let p1 : TaperedStrip.domain β := ⟨(1, 0), by simp [TaperedStrip.domain, hβ.le]⟩
    have heq : H p0 = H p1 := by
      apply Subtype.ext
      rw [hval, hval]
      change A.zeroApexCoordinates q w v (0, 0) = A.zeroApexCoordinates q w v (1, 0)
      rw [zeroApexCoordinates_bottom, zeroApexCoordinates_bottom,
        lineMap_apply_zero, lineMap_apply_one]
      exact h
    have h01 := congrArg (fun z : TaperedStrip.domain β => (z : ℝ × ℝ).1) (H.injective heq)
    norm_num [p0, p1] at h01
  obtain ⟨e, he, heval⟩ := TaperedStrip.exists_segmentDomain_homeomorph hqw hβ
  let G := e.symm.trans H
  have hbase (p : TaperedStrip.segmentDomain q w β) :
      lineMap q w (e.symm p : ℝ × ℝ).1 = (p : E × ℝ).1 := by
    have h := congrArg Prod.fst (heval (e.symm p))
    rw [e.apply_symm_apply] at h
    exact h.symm
  have ht (p : TaperedStrip.segmentDomain q w β) :
      (e.symm p : ℝ × ℝ).2 = (p : E × ℝ).2 := by
    have h := congrArg Prod.snd (heval (e.symm p))
    rw [e.apply_symm_apply] at h
    exact h.symm
  let b : TaperedStrip.domain β → TaperedStrip.domain β := fun z =>
    ⟨((z : ℝ × ℝ).1, 0), z.property.1, le_rfl, mul_nonneg hβ.le z.property.1.1⟩
  have hb (z : TaperedStrip.domain β) : (H (b z) : E) = lineMap q w (z : ℝ × ℝ).1 := by
    rw [hval]
    exact A.zeroApexCoordinates_bottom q w v (z : ℝ × ℝ).1
  have hcollapse (z : TaperedStrip.domain β) :
      (b z : ℝ × ℝ) = (0, 0) ↔ (z : ℝ × ℝ) = (0, 0) := by
    constructor
    · intro hz
      have hs : (z : ℝ × ℝ).1 = 0 := congrArg Prod.fst hz
      apply Prod.ext hs
      exact le_antisymm (by simpa only [hs, mul_zero] using z.property.2.2) z.property.2.1
    · intro hz
      change ((z : ℝ × ℝ).1, 0) = (0, 0)
      rw [hz]
  have hedgeSide (p : TaperedStrip.segmentDomain q w β) :
      (p : E × ℝ).1 ∈ segment ℝ u v ↔ (G p : E) ∈ segment ℝ u v := by
    rw [← hbase p, ← hb (e.symm p)]
    exact (hside (b (e.symm p))).trans (hside (e.symm p)).symm
  have hedgeNeg (p : TaperedStrip.segmentDomain q w β) :
      (p : E × ℝ).1 ∈ segment ℝ q u ↔ (G p : E) ∈ segment ℝ q u := by
    rw [← hbase p, ← hb (e.symm p)]
    exact (hneg (b (e.symm p))).trans ((hcollapse (e.symm p)).trans (hneg (e.symm p)).symm)
  have hedgeFar (p : TaperedStrip.segmentDomain q w β) :
      (p : E × ℝ).1 ∈ segment ℝ q v ↔ (G p : E) ∈ segment ℝ q v := by
    rw [← hbase p, ← hb (e.symm p)]
    exact (hfar (b (e.symm p))).trans ((hcollapse (e.symm p)).trans (hfar (e.symm p)).symm)
  refine ⟨G, he.symm.trans hH, ?_, fun p => (hheight (e.symm p)).trans (ht p),
    ?_, hsub, hsection, ?_⟩
  · intro p
    change (H (e.symm p) : E) = _
    calc
      _ = lineMap q w (e.symm p : ℝ × ℝ).1 +
          (e.symm p : ℝ × ℝ).2 • A.heightRay w v := by
        rw [hval, zeroApexCoordinates_apply, lineMap_apply_module']
        module
      _ = _ := by rw [hbase p, ht p]
  · intro p hp
    have ht0 : (e.symm p : ℝ × ℝ).2 = 0 := (ht p).trans hp
    have hp0 : (e.symm p : ℝ × ℝ) = ((e.symm p : ℝ × ℝ).1, 0) := Prod.ext rfl ht0
    change (H (e.symm p) : E) = _
    rw [hval, hp0, zeroApexCoordinates_bottom]
    exact hbase p
  · intro f hf hfs p
    rcases Finset.eq_pair_of_subset_triple hf hfs with rfl | rfl | rfl
    · simpa only [Finset.coe_pair, convexHull_pair] using hedgeNeg p
    · simpa only [Finset.coe_pair, convexHull_pair] using hedgeFar p
    · simpa only [Finset.coe_pair, convexHull_pair] using hedgeSide p






theorem exists_exceptional_triangle_geometric_edge_collar (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hi : AffineIndependent ℝ ![q, u, v]) (hq : A q = 0)
    (hu : A u < 0) (hv : 0 < A v) {β : ℝ} (hβ : 0 < β) (hβv : β < A v) :
    ∃ G : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β ≃ₜ
        convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)),
      G.IsFinitePL ∧ (∀ p, A (G p) = (p : E × ℝ).2) ∧
        (∀ p : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β,
          (p : E × ℝ).2 = 0 → (G p : E) = (p : E × ℝ).1) ∧
        (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ⊆
          convexHull ℝ (insert q ({u, v} : Set E))) ∧
        (convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} =
          segment ℝ q (A.zeroCrossing u v)) ∧
        ∀ e : Finset E, e.card = 2 → e ⊆ {q, u, v} →
          ∀ p : TaperedStrip.segmentDomain q (A.zeroCrossing u v) β,
            (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
              (G p : E) ∈ convexHull ℝ (e : Set E) := by
  obtain ⟨G, hG, _, hrest⟩ :=
    A.exists_exceptional_triangle_geometric_edge_collar_with_formula hi hq hu hv hβ hβv
  exact ⟨G, hG, hrest⟩

end AffineMap
