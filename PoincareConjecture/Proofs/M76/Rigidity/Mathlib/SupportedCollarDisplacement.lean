import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapseHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactStripFrontier
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteLabelSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T1Space Y]

open Classical in

theorem exists_supported_displacement (L : SimplicialComplex ℝ E)
    (hL : L.faces.Finite) {delta r : ℝ} (hr : 0 < r) (hwidth : 2 * r < delta)
    (c : E × ℝ → X) (hc : ContinuousOn c (L.space ×ˢ Icc (-delta) delta))
    (hi : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-delta) delta : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (L.space ×ˢ Ioo (-delta) delta)))
    (q : C(X, Y)) (a b : Y) (hab : a ≠ b)
    (hphase : ∀ x ∈ L.space, q (c (x, 0)) ∈ ({a, b} : Set Y)) :
    ∃ w : C(unitInterval × X, ℝ),
      (∀ y : X, w (0, y) = 0) ∧
      (∀ (s : unitInterval) (z : E × ℝ), z ∈ L.space ×ˢ Icc (-delta) delta →
        w (s, c z) = (s : ℝ) * (if q (c (z.1, 0)) = a then 1 else -1) *
          displacement r z.2) ∧
      (∀ (s : unitInterval) (y : X),
        y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) → w (s, y) = 0) ∧
      (∀ (s : unitInterval) (x : E), x ∈ L.space → w (s, c (x, 0)) = 0) ∧
      (∀ (s : unitInterval) (z : E × ℝ),
        z ∈ L.space ×ˢ ({-delta, delta} : Set ℝ) → w (s, c z) = 0) ∧
      (∀ (s : unitInterval) (y : X), |w (s, y)| ≤ r) ∧
      ∀ z : E × ℝ, z ∈ L.space ×ˢ Icc (-r) r →
        (q (c (z.1, 0)) = a → w (1, c z) = z.2) ∧
        (q (c (z.1, 0)) = b → w (1, c z) = -z.2) := by
  have hdelta : 0 < delta := by linarith
  let P : Set (E × ℝ) := L.space ×ˢ Icc (-delta) delta
  let A : Set X := c '' P
  let sigma : E → ℝ := fun x => if q (c (x, 0)) = a then 1 else -1
  have hbase (x : E) (hx : x ∈ L.space) : (x, (0 : ℝ)) ∈ P :=
    ⟨hx, by constructor <;> linarith⟩
  have hcbase : ContinuousOn (fun x : E => c (x, 0)) L.space :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn hbase
  have hlabel : ContinuousOn (fun x : E => q (c (x, 0))) L.space :=
    q.continuous.comp_continuousOn hcbase
  have hsigma : ContinuousOn sigma L.space :=
    (L.finitePiecewiseAffineOn_finite_label hL hlabel
      ((finite_singleton b).insert a) hphase
      (fun y => if y = a then (1 : ℝ) else -1)).continuousOn
  have habsigma (x : E) : |sigma x| = 1 := by
    dsimp only [sigma]
    split <;> norm_num
  have hA : IsCompact A :=
    ((L.isCompact_space_of_finite hL).prod isCompact_Icc).image_of_continuousOn hc
  obtain ⟨k, hk, hleft, _, hkmap⟩ := hi.exists_inverse_on_image
  have hkA : Continuous (fun y : A => k y) := hk.domRestrict
  let base : A → L.space := fun y => ⟨(k y).1, (hkmap y.property).1⟩
  have hbasecont : Continuous base := hkA.fst.subtype_mk _
  have hsign : Continuous (fun z : unitInterval × A => sigma (k z.2).1) :=
    (hsigma.domRestrict.comp hbasecont).comp continuous_snd
  have htime : Continuous (fun z : unitInterval × A =>
      displacement r (k z.2).2) :=
    (continuous_displacement r).comp (hkA.comp continuous_snd).snd
  let G : C(unitInterval × A, ℝ) :=
    ⟨fun z => (z.1 : ℝ) * sigma (k z.2).1 * displacement r (k z.2).2,
      ((continuous_subtype_val.comp continuous_fst).mul hsign).mul htime⟩
  let H : C(unitInterval × X, ℝ) := ⟨fun _ => 0, continuous_const⟩
  have hendmem {t : ℝ} (ht : t ∈ ({-delta, delta} : Set ℝ)) :
      t ∈ Icc (-delta) delta := by
    rcases ht with ht | ht
    · rw [ht]
      exact ⟨le_rfl, by linarith⟩
    · rw [ht]
      exact ⟨by linarith, le_rfl⟩
  have henddisp {t : ℝ} (ht : t ∈ ({-delta, delta} : Set ℝ)) :
      displacement r t = 0 := by
    apply displacement_eq_zero_of_two_le_abs hr.le
    rcases ht with ht | ht
    · rw [ht, abs_neg, abs_of_pos hdelta]
      exact hwidth.le
    · rw [ht, abs_of_pos hdelta]
      exact hwidth.le
  have hfront : ∀ (s : unitInterval) (y : A), (y : X) ∈ frontier A →
      G (s, y) = H (s, y) := by
    intro s y hy
    obtain ⟨z, hz, hzy⟩ := frontier_compact_strip_subset_ends
      (L.isCompact_space_of_finite hL) hc ho hy
    have hzP : z ∈ P := ⟨hz.1, hendmem hz.2⟩
    change (s : ℝ) * sigma (k y).1 * displacement r (k y).2 = 0
    rw [← hzy, hleft z hzP, henddisp hz.2, mul_zero]
  obtain ⟨w, hinner, houter⟩ :=
    ContinuousMap.exists_paste_of_eq_on_frontier hA.isClosed G H hfront
  have hvalue (s : unitInterval) (z : E × ℝ) (hz : z ∈ P) :
      w (s, c z) = (s : ℝ) * sigma z.1 * displacement r z.2 := by
    have h := hinner s ⟨c z, ⟨z, hz, rfl⟩⟩
    change w (s, c z) = (s : ℝ) * sigma (k (c z)).1 *
      displacement r (k (c z)).2 at h
    simpa only [hleft z hz] using h
  have hzero (y : X) : w (0, y) = 0 := by
    by_cases hy : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hvalue 0 z hz]
      change (0 : ℝ) * sigma z.1 * displacement r z.2 = 0
      rw [zero_mul, zero_mul]
    · exact houter 0 y (fun h => hy (interior_subset h))
  have hfixed (s : unitInterval) (y : X)
      (hy : y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r))) : w (s, y) = 0 := by
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hyA
      have ht : 2 * r ≤ |z.2| := by
        by_contra ht
        have ht' : |z.2| < 2 * r := lt_of_not_ge ht
        exact hy ⟨z, ⟨hz.1, abs_lt.mp ht'⟩, rfl⟩
      rw [hvalue s z hz, displacement_eq_zero_of_two_le_abs hr.le ht, mul_zero]
    · exact houter s y (fun h => hyA (interior_subset h))
  refine ⟨w, hzero, hvalue, hfixed, ?_, ?_, ?_, ?_⟩
  · intro s x hx
    rw [hvalue s (x, 0) (hbase x hx)]
    have hv : displacement r 0 = 0 := by
      rw [displacement, height_of_mem hr.le (show (0 : ℝ) ∈ Icc (-r) r by
        constructor <;> linarith), sub_self]
    rw [hv, mul_zero]
  · intro s z hz
    rw [hvalue s z ⟨hz.1, hendmem hz.2⟩, henddisp hz.2, mul_zero]
  · intro s y
    by_cases hy : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [hvalue s z hz]
      simpa only [abs_mul, habsigma, mul_one] using
        (abs_time_displacement_le hr.le s.property z.2)
    · rw [houter s y (fun h => hy (interior_subset h))]
      change |(0 : ℝ)| ≤ r
      simpa only [abs_zero] using hr.le
  · intro z hz
    have hzP : z ∈ P := ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hw : w (1, c z) = sigma z.1 * z.2 := by
      rw [hvalue 1 z hzP]
      change (1 : ℝ) * sigma z.1 * displacement r z.2 = sigma z.1 * z.2
      rw [one_mul, displacement, height_of_mem hr.le hz.2, sub_zero]
    constructor
    · intro ha
      rw [hw]
      simp only [sigma, if_pos ha, one_mul]
    · intro hb
      have hne : q (c (z.1, 0)) ≠ a := by
        rw [hb]
        exact Ne.symm hab
      rw [hw]
      simp only [sigma, if_neg hne, neg_one_mul]

end CollarCollapse
