import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativeCorner
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_relative_circle_endpoint_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (p : ℝ) [Fact (0 < p)] {R : Set X} (q : R → AddCircle p)
    {a b theta d : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (htheta : theta = a ∨ theta = b) (hd : (d : AddCircle p) = (theta : AddCircle p))
    (psi ell : E →ᴬ[ℝ] ℝ) (u v : E) (T : OpenPartialHomeomorph X E)
    (hpu : psi.contLinear u = 1) (hlv : ell.contLinear v = 1)
    (hpv : psi.contLinear v = 0) {x : X} (hx : x ∈ T.source)
    (hpx : psi (T x) = 0) (hlx : ell (T x) = 0)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    (hR : ∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y))
    (hB : ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0)
    (hq : ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p)) :
    ∃ (lambda : E →ᴬ[ℝ] ℝ) (G : OpenPartialHomeomorph X E),
      x ∈ G.source ∧ G.source ⊆ T.source ∧ psi (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      (∀ y ∈ G.source, psi (T y) = 0 → ell (T y) = 0 → G y = T y) ∧
      (∀ y ∈ G.source,
        (∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
          0 ≤ psi (G y)) ∧
      (∀ y ∈ G.source,
        (y ∈ frontier R ∧ ∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
      ∀ y ∈ G.source,
        (∃ hy : y ∈ R, q ⟨y, hy⟩ = (theta : AddCircle p)) ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  classical
  let m := min a (min (p - b) (b - a))
  let eta := m / 2
  have hm : 0 < m := lt_min ha (lt_min (sub_pos.mpr hb) (sub_pos.mpr hab))
  have heta : 0 < eta := half_pos hm
  have hetam : eta < m := half_lt_self hm
  have hea : eta < a := hetam.trans_le (min_le_left _ _)
  have heb : eta < p - b :=
    hetam.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heab : eta < b - a :=
    hetam.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let W : Set E := ell ⁻¹' Ioo (-eta) eta
  have hW : IsOpen W := isOpen_Ioo.preimage ell.continuous
  let I := OpenPartialHomeomorph.ofSet W hW
  let T' := T.trans I
  have hxT : x ∈ T'.source := by
    refine ⟨hx, ?_⟩
    change ell (T x) ∈ Ioo (-eta) eta
    rw [hlx]
    exact ⟨neg_neg_of_pos heta, heta⟩
  have hI : I ∈ piecewiseAffineGroupoid E :=
    ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW,
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW⟩
  have hT' (i : ι) : (e i).symm.trans T' ∈ piecewiseAffineGroupoid E := by
    simpa only [T', OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hT i) hI
  let eps : ℝ := if theta = a then 1 else -1
  have heps : eps = 1 ∨ eps = -1 := by unfold eps; split_ifs <;> simp
  have hepssq : eps * eps = 1 := by rcases heps with h | h <;> rw [h] <;> norm_num
  have hepsne : eps ≠ 0 := by rcases heps with h | h <;> rw [h] <;> norm_num
  let lambda : E →ᴬ[ℝ] ℝ := eps • ell
  have hlamzero (z : E) : lambda z = 0 ↔ ell z = 0 := by
    change eps * ell z = 0 ↔ _
    simp only [mul_eq_zero, hepsne, false_or]
  have hlamv : lambda.contLinear (eps • v) = 1 := by
    change eps * ell.contLinear (eps • v) = 1
    rw [map_smul, smul_eq_mul, hlv, mul_one, hepssq]
  have hpv' : psi.contLinear (eps • v) = 0 := by rw [map_smul, hpv, smul_zero]
  have hrep (y : X) (hy : y ∈ T'.source) : ell (T' y) + theta ∈ Ico (0 : ℝ) p := by
    have hyW : ell (T' y) ∈ Ioo (-eta) eta := hy.2
    rcases htheta with rfl | rfl
    · constructor <;> linarith [hyW.1, hyW.2]
    · constructor <;> linarith [hyW.1, hyW.2]
  have hq' (y : R) (hy : (y : X) ∈ T'.source) :
      q y = ((ell (T' y) + theta : ℝ) : AddCircle p) := by
    change q y = ((ell (T y) + theta : ℝ) : AddCircle p)
    rw [hq y hy.1, AddCircle.coe_add, hd, ← AddCircle.coe_add]
  have hqarc (y : R) (hy : (y : X) ∈ T'.source) :
      q y ∈ AddCircle.closedIntervalArc p a b ↔ 0 ≤ lambda (T' y) := by
    rw [hq' y hy, AddCircle.coe_mem_closedIntervalArc_iff p ha.le hb (hrep y hy)]
    have hyW : ell (T' y) ∈ Ioo (-eta) eta := hy.2
    change (a ≤ ell (T' y) + theta ∧ ell (T' y) + theta ≤ b) ↔ 0 ≤ eps * ell (T' y)
    rcases htheta with rfl | rfl
    · simp only [eps, if_true, one_mul]
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith [hyW.2]
    · have hne : theta ≠ a := ne_of_gt hab
      simp only [eps, if_neg hne, neg_one_mul]
      constructor
      · intro h; linarith [h.2]
      · intro h; constructor <;> linarith [hyW.1]
  have hqzero (y : R) (hy : (y : X) ∈ T'.source) :
      q y = (theta : AddCircle p) ↔ lambda (T' y) = 0 := by
    have hthetaI : theta ∈ Ico (0 : ℝ) (0 + p) := by
      rcases htheta with rfl | rfl <;> constructor <;> linarith
    have hyI : ell (T' y) + theta ∈ Ico (0 : ℝ) (0 + p) := by
      simpa only [zero_add] using hrep y hy
    rw [hq' y hy, AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hthetaI, hlamzero]
    exact add_eq_right
  obtain ⟨G, hGs, hG, hfix, hquad, hold, hnew⟩ :=
    exists_relative_phase_corner e T' hT' psi lambda u (eps • v) hpu hlamv hpv'
  have hGsub : G.source ⊆ T.source := fun _ hy => (hGs.subset hy).1
  have hpx' : psi (T' x) = 0 := hpx
  have hlx' : lambda (T' x) = 0 := (hlamzero _).mpr hlx
  have hdomain (y : X) (hy : y ∈ T'.source) :
      (∃ hyR : y ∈ R, q ⟨y, hyR⟩ ∈ AddCircle.closedIntervalArc p a b) ↔
        0 ≤ psi (T' y) ∧ 0 ≤ lambda (T' y) := by
    constructor
    · rintro ⟨hyR, hqR⟩
      exact ⟨(hR y hy.1).mp hyR, (hqarc ⟨y, hyR⟩ hy).mp hqR⟩
    · rintro ⟨hp, hl⟩
      have hyR := (hR y hy.1).mpr hp
      exact ⟨hyR, (hqarc ⟨y, hyR⟩ hy).mpr hl⟩
  refine ⟨lambda, G, hGs.symm.subset hxT, hGsub, ?_, hG, ?_, ?_, ?_, ?_⟩
  · rw [hfix x hpx' hlx']
    exact hpx'
  · intro y _ hp hl
    exact hfix y hp ((hlamzero _).mpr hl)
  · intro y hy
    exact (hdomain y (hGs.subset hy)).trans (hquad y)
  · intro y hy
    have hy' := hGs.subset hy
    rw [hB y hy'.1, hdomain y hy']
    have hsame : psi (T y) = psi (T' y) := rfl
    rw [hsame]
    exact (show (psi (T' y) = 0 ∧ 0 ≤ psi (T' y) ∧ 0 ≤ lambda (T' y)) ↔
      psi (T' y) = 0 ∧ 0 ≤ lambda (T' y) from
        ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.ge, h.2⟩⟩).trans (hold y)
  · intro y hy
    have hy' := hGs.subset hy
    apply Iff.trans _ (hnew y)
    constructor
    · rintro ⟨hyR, hqR⟩
      exact ⟨(hqzero ⟨y, hyR⟩ hy').mp hqR, (hR y hy'.1).mp hyR⟩
    · rintro ⟨hl, hp⟩
      have hyR := (hR y hy'.1).mpr hp
      exact ⟨hyR, (hqzero ⟨y, hyR⟩ hy').mpr hl⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
