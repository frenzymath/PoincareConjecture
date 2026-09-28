import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcGerms
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateSecondReflection

set_option autoImplicit false

open Set Filter AffineMap CoordinateHalfBoxes
open scoped Topology

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

private theorem second_lineMap_eq_slope
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {a b : E} {t : ℝ}
    (hzero : f.symm (lineMap a b t) = 0) (u : ℝ) :
    (f.symm (lineMap a b u)).1.2 =
      ((f.symm b).1.2 - (f.symm a).1.2) * (u - t) := by
  have hform (v : ℝ) : (f.symm (lineMap a b v)).1.2 =
      v * ((f.symm b).1.2 - (f.symm a).1.2) + (f.symm a).1.2 := by
    have h := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2)
      (f.symm.toAffineEquiv.apply_lineMap a b v)
    simpa only [fst_lineMap, snd_lineMap, lineMap_apply_ring',
      ContinuousAffineEquiv.coe_coe] using h
  have ht := hform t
  rw [hzero] at ht
  change 0 = t * ((f.symm b).1.2 - (f.symm a).1.2) + (f.symm a).1.2 at ht
  rw [hform]
  nlinarith

private theorem cutArcs_pullback_of_positive_slope
    (P : Polygon E (n + 3)) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hf0 : f 0 = P.edgeCut t i) {r : ℝ}
    (hsection : ∀ x ∈ box r, f x ∈ P.boundary ℝ ↔ x.1.1 = 0 ∧ x.2 = 0)
    (hlocal : ∀ x ∈ box r,
      (f x ∈ P.boundary ℝ ↔ f x ∈ P.edgeSet ℝ i) ∧
      (f x ∈ P.cutArc t i ↔
        f x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc (t i) 1) ∧
      (f x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
        f x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc 0 (t i)))
    (hslope : 0 < (f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) :
    ∀ x ∈ box r,
      (f x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
      (f x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
        x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0) := by
  have hzero : f.symm (lineMap (P i) (P (finRotate (n + 3) i)) (t i)) = 0 := by
    change f.symm (P.edgeCut t i) = 0
    rw [← hf0, f.symm_apply_apply]
  have harcboundary (k : Fin (n + 3)) : P.cutArc t k ⊆ P.boundary ℝ :=
    (subset_iUnion (fun j => P.cutArc t j) k).trans
      (P.iUnion_cutArc t (fun j => ⟨(ht j).1.le, (ht j).2.le⟩)).subset
  intro x hx
  have hhalves (hxb : f x ∈ P.boundary ℝ) :
      (f x ∈ P.cutArc t i ↔ 0 ≤ x.1.2) ∧
      (f x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔ x.1.2 ≤ 0) := by
    obtain ⟨u, hu, huf⟩ := (hlocal x hx).1.mp hxb
    have hcoordinate : x.1.2 =
        ((f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) * (u - t i) := by
      simpa only [huf, f.symm_apply_apply] using second_lineMap_eq_slope f hzero u
    have hupper : f x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc (t i) 1 ↔
        t i ≤ u := by
      constructor
      · rintro ⟨v, hv, hvf⟩
        have hvu := lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)
          (hvf.trans huf.symm)
        exact hvu ▸ hv.1
      · intro htu
        exact ⟨u, ⟨htu, hu.2⟩, huf⟩
    have hlower : f x ∈ lineMap (P i) (P (finRotate (n + 3) i)) '' Icc 0 (t i) ↔
        u ≤ t i := by
      constructor
      · rintro ⟨v, hv, hvf⟩
        have hvu := lineMap_injective ℝ (P.edge_endpoints_ne_of_injective hinj i)
          (hvf.trans huf.symm)
        exact hvu ▸ hv.2
      · intro hut
        exact ⟨u, ⟨hu.1, hut⟩, huf⟩
    have hpositive : 0 ≤ x.1.2 ↔ t i ≤ u := by
      rw [hcoordinate]
      simpa only [mul_zero, sub_nonneg] using
        (mul_le_mul_iff_of_pos_left hslope :
          ((f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) * 0 ≤
            ((f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) * (u - t i) ↔
          0 ≤ u - t i)
    have hnegative : x.1.2 ≤ 0 ↔ u ≤ t i := by
      rw [hcoordinate]
      simpa only [mul_zero, sub_nonpos] using
        (mul_le_mul_iff_of_pos_left hslope :
          ((f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) * (u - t i) ≤
            ((f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2) * 0 ↔
          u - t i ≤ 0)
    exact ⟨(hlocal x hx).2.1.trans (hupper.trans hpositive.symm),
      (hlocal x hx).2.2.trans (hlower.trans hnegative.symm)⟩
  constructor
  · constructor
    · intro hxa
      have hxb := harcboundary i hxa
      exact ⟨(hsection x hx).mp hxb |>.1, (hsection x hx).mp hxb |>.2,
        (hhalves hxb).1.mp hxa⟩
    · rintro ⟨hxheight, hxplane, hxsign⟩
      exact (hhalves ((hsection x hx).mpr ⟨hxheight, hxplane⟩)).1.mpr hxsign
  · constructor
    · intro hxa
      have hxb := harcboundary ((finRotate (n + 3)).symm i) hxa
      exact ⟨(hsection x hx).mp hxb |>.1, (hsection x hx).mp hxb |>.2,
        (hhalves hxb).2.mp hxa⟩
    · rintro ⟨hxheight, hxplane, hxsign⟩
      exact (hhalves ((hsection x hx).mpr ⟨hxheight, hxplane⟩)).2.mpr hxsign

theorem exists_oriented_affine_cut_box
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hf0 : f 0 = P.edgeCut t i)
    {R : ℝ} (hR : 0 < R)
    (hsection : ∀ x ∈ box R, f x ∈ P.boundary ℝ ↔ x.1.1 = 0 ∧ x.2 = 0) :
    ∃ (g : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ),
      0 < r ∧ r ≤ R ∧
      (g = f ∨ g = secondReflection.toContinuousAffineEquiv.trans f) ∧
      g 0 = P.edgeCut t i ∧ (∀ a, g '' box a = f '' box a) ∧
      ∀ x ∈ box r,
        (g x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
        (g x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
          x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0) := by
  obtain ⟨V, hVsub, hV, hqV⟩ :=
    mem_nhds_iff.mp (P.eventually_cutArcs_at_edgeCut hP hinj t ht i)
  have hfV : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  have hzeroV : (0 : (ℝ × ℝ) × ℝ) ∈ f ⁻¹' V := by
    change f 0 ∈ V
    rw [hf0]
    exact hqV
  obtain ⟨ρ, hρ, hρV⟩ := exists_box_subset hfV hzeroV
  let δ := min R ρ
  have hδ : 0 < δ := lt_min hR hρ
  have hsmall : box δ ⊆ box R := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hδV : f '' box δ ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    apply hρV
    apply (show box δ ⊆ box ρ from ?_) hx
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall (min_le_right _ _)
  have hzero : f.symm (lineMap (P i) (P (finRotate (n + 3) i)) (t i)) = 0 := by
    change f.symm (P.edgeCut t i) = 0
    rw [← hf0, f.symm_apply_apply]
  let d := (f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2
  have hd : d ≠ 0 := by
    intro hd
    let z : (ℝ × ℝ) × ℝ := ((0, δ / 2), 0)
    have hz : z ∈ box δ := by
      change ((-δ ≤ (0 : ℝ) ∧ 0 ≤ δ) ∧ (-δ ≤ δ / 2 ∧ δ / 2 ≤ δ)) ∧
        -δ ≤ 0 ∧ 0 ≤ δ
      exact ⟨⟨⟨neg_nonpos.mpr hδ.le, hδ.le⟩, by constructor <;> linarith⟩,
        neg_nonpos.mpr hδ.le, hδ.le⟩
    have hzb : f z ∈ P.boundary ℝ := (hsection z (hsmall hz)).mpr ⟨rfl, rfl⟩
    obtain ⟨u, _, huf⟩ := (hVsub (hδV ⟨z, hz, rfl⟩)).1.mp hzb
    have hcoord := second_lineMap_eq_slope f hzero u
    change (f.symm (lineMap (P i) (P (finRotate (n + 3) i)) u)).1.2 = d * (u - t i)
      at hcoord
    rw [huf, f.symm_apply_apply, hd, zero_mul] at hcoord
    change δ / 2 = 0 at hcoord
    linarith
  have hfinish (g : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
      (hchoice : g = f ∨ g = secondReflection.toContinuousAffineEquiv.trans f)
      (hg0 : g 0 = P.edgeCut t i) (himage : ∀ a, g '' box a = f '' box a)
      (hslope : 0 < (g.symm (P (finRotate (n + 3) i))).1.2 - (g.symm (P i)).1.2) :
      ∀ x ∈ box δ,
        (g x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
        (g x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
          x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0) := by
    apply cutArcs_pullback_of_positive_slope P hinj t ht i g hg0 ?_ ?_ hslope
    · intro x hx
      rcases hchoice with rfl | rfl
      · exact hsection x (hsmall hx)
      · change f (secondReflection x) ∈ P.boundary ℝ ↔ x.1.1 = 0 ∧ x.2 = 0
        simpa only [secondReflection_apply] using
          hsection (secondReflection x)
            (hsmall ((secondReflection_mem_box δ x).mpr hx))
    · intro x hx
      apply hVsub
      apply hδV
      rw [← himage δ]
      exact ⟨x, hx, rfl⟩
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · let g := secondReflection.toContinuousAffineEquiv.trans f
    have hg0 : g 0 = P.edgeCut t i := by
      change f (secondReflection 0) = P.edgeCut t i
      rw [secondReflection_zero, hf0]
    have himage (a : ℝ) : g '' box a = f '' box a := image_secondReflection_trans f a
    have hslope : 0 < (g.symm (P (finRotate (n + 3) i))).1.2 -
        (g.symm (P i)).1.2 := by
      simp only [g, secondReflection_trans_symm_apply, secondReflection_apply]
      change (f.symm (P (finRotate (n + 3) i))).1.2 - (f.symm (P i)).1.2 < 0 at hneg
      linarith
    exact ⟨g, δ, hδ, min_le_left _ _, Or.inr rfl, hg0, himage,
      hfinish g (Or.inr rfl) hg0 himage hslope⟩
  · exact ⟨f, δ, hδ, min_le_left _ _, Or.inl rfl, hf0, fun _ => rfl,
      hfinish f (Or.inl rfl) hf0 (fun _ => rfl) hpos⟩

end Polygon
