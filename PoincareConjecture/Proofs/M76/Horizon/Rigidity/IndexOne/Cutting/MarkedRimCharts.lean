import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativeEndpointChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeChartRestriction
import PoincareConjecture.Proofs.M76.Wall.Mathlib.AffineHalfspaceProduct
import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_relative_circle_endpoint_chart_with_tangent
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
    ∃ (lambda : E →ᴬ[ℝ] ℝ) (v' : E) (G : OpenPartialHomeomorph X E),
      psi.contLinear v' = 0 ∧ lambda.contLinear v' = 1 ∧
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
  refine ⟨lambda, eps • v, G, hpv', hlamv, hGs.symm.subset hxT, hGsub, ?_, hG, ?_, ?_, ?_, ?_⟩
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

theorem exists_relative_shifted_circle_endpoint_chart_with_tangent
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (p : ℝ) [Fact (0 < p)] {R : Set X} (q : R → AddCircle p)
    {c a b theta d : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (htheta : theta = a ∨ theta = b) (hd : (d : AddCircle p) = (theta : AddCircle p))
    (psi ell : E →ᴬ[ℝ] ℝ) (u v : E) (T : OpenPartialHomeomorph X E)
    (hpu : psi.contLinear u = 1) (hlv : ell.contLinear v = 1)
    (hpv : psi.contLinear v = 0) {x : X} (hx : x ∈ T.source)
    (hpx : psi (T x) = 0) (hlx : ell (T x) = 0)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    (hR : ∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y))
    (hB : ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0)
    (hq : ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p)) :
    ∃ (lambda : E →ᴬ[ℝ] ℝ) (v' : E) (G : OpenPartialHomeomorph X E),
      psi.contLinear v' = 0 ∧ lambda.contLinear v' = 1 ∧
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
  let q' : R → AddCircle p := fun y => q y - (c : AddCircle p)
  have hphase (y : R) (t : ℝ) : q' y = ((t - c : ℝ) : AddCircle p) ↔
      q y = (t : AddCircle p) := by
    change q y - (c : AddCircle p) = ((t - c : ℝ) : AddCircle p) ↔ _
    rw [AddCircle.coe_sub, sub_left_inj]
  have harc (y : R) : q' y ∈ AddCircle.closedIntervalArc p (a - c) (b - c) ↔
      q y ∈ AddCircle.closedIntervalArc p a b := by
    constructor
    · rintro ⟨t, ht, hty⟩
      refine ⟨t + c, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      exact ((hphase y (t + c)).mp (by simpa only [add_sub_cancel_right] using hty.symm)).symm
    · rintro ⟨t, ht, hty⟩
      exact ⟨t - c, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ((hphase y t).mpr hty.symm).symm⟩
  have htheta' : theta - c = a - c ∨ theta - c = b - c :=
    htheta.imp (fun h => congrArg (fun t => t - c) h)
      (fun h => congrArg (fun t => t - c) h)
  have hd' : ((d - c : ℝ) : AddCircle p) = ((theta - c : ℝ) : AddCircle p) := by
    simp only [AddCircle.coe_sub, hd]
  have hq' (y : R) (hy : (y : X) ∈ T.source) :
      q' y = ((ell (T y) + (d - c) : ℝ) : AddCircle p) := by
    change q y - (c : AddCircle p) = _
    rw [hq y hy, ← AddCircle.coe_sub]
    congr 1
    ring
  obtain ⟨lambda, v', G, hpv', hlv', hxG, hGT, hpxG, hG, hfix, hGN, hGB, hGS⟩ :=
    exists_relative_circle_endpoint_chart_with_tangent e p q'
      (by linarith : 0 < a - c) (by linarith : a - c < b - c)
      (by linarith : b - c < p) htheta' hd' psi ell u v T
      hpu hlv hpv hx hpx hlx hT hR hB hq'
  refine ⟨lambda, v', G, hpv', hlv', hxG, hGT, hpxG, hG, hfix, ?_, ?_, ?_⟩
  · intro y hy
    simpa only [harc] using hGN y hy
  · intro y hy
    simpa only [harc] using hGB y hy
  · intro y hy
    simpa only [hphase] using hGS y hy

theorem exists_intrinsic_signed_rim_chart
    {X : Type*} [TopologicalSpace X] {N S O : Set X}
    (G : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (psi lambda : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (u v : Fin 3 → ℝ)
    (hpu : psi.contLinear u = 1) (hpv : psi.contLinear v = 0)
    (hlv : lambda.contLinear v = 1)
    (hN : ∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y))
    (hS : ∀ y ∈ G.source, y ∈ S ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hO : ∀ y ∈ G.source, y ∈ O ↔ psi (G y) = 0 ∧ 0 ≤ lambda (G y))
    (x : frontier N) (hx : (x : X) ∈ G.source) :
    ∃ T : OpenPartialHomeomorph (frontier N) (ℝ × ℝ),
      x ∈ T.source ∧
      (∀ y ∈ T.source, (y : X) ∈ S ↔ 0 ≤ (T y).2) ∧
      (∀ y ∈ T.source, (y : X) ∈ O ↔ (T y).2 ≤ 0) ∧
      ∀ y ∈ T.source, (y : X) ∈ S ∩ O ↔ (T y).2 = 0 := by
  have hpne : psi.toAffineMap.linear ≠ 0 := by
    intro h
    have hv : psi.toAffineMap.linear u = 1 := hpu
    rw [h] at hv
    norm_num at hv
  obtain ⟨a, r, hra, har, ha⟩ :=
    psi.toAffineMap.exists_zeroLevel_coordinates (F := Fin 2 → ℝ) hpne (by simp)
  let Q : Set (Fin 3 → ℝ) := {z | psi z = 0}
  let H : Q ≃ₜ (Fin 2 → ℝ) :=
    { toFun := fun z => r z
      invFun := fun z => ⟨a z, ha z⟩
      left_inv := fun z => Subtype.ext (har z.property)
      right_inv := hra
      continuous_toFun := r.continuous.comp continuous_subtype_val
      continuous_invFun := a.continuous.subtype_mk _ }
  have himage : G.IsImage (frontier N) Q :=
    G.isImage_frontier_of_affine_nonneg psi hpne hN
  obtain ⟨T0, hT0s, _, hT0, _⟩ := himage.exists_subtype_chart x hx
  let ell : (Fin 2 → ℝ) →ᴬ[ℝ] ℝ := -(lambda.comp a)
  let z : Fin 3 → ℝ := G x
  have hz : psi z = 0 := (himage.apply_mem_iff hx).mpr x.property
  have hzv : psi (z + v) = 0 := by
    simpa only [vadd_eq_add, hpv, hz, add_zero, add_comm] using psi.map_vadd z v
  let w : Fin 2 → ℝ := r (z + v) - r z
  have hw : ell.contLinear (-w) = 1 := by
    have hdiff : ell (r (z + v)) - ell (r z) = -1 := by
      change -lambda (a (r (z + v))) - -lambda (a (r z)) = -1
      rw [har hzv, har hz]
      have hval : lambda (z + v) = lambda z + 1 := by
        simpa only [vadd_eq_add, hlv, add_comm] using lambda.map_vadd z v
      rw [hval]
      ring
    have hlinear : ell.contLinear w = -1 := by
      have h := ell.map_vadd (r z) w
      have hsum : w + r z = r (z + v) := sub_add_cancel _ _
      rw [vadd_eq_add, vadd_eq_add, hsum] at h
      linarith
    rw [map_neg, hlinear]
    norm_num
  obtain ⟨J, hJ⟩ := ell.exists_halfspace_product_homeomorph (F := ℝ) (-w) hw (by simp)
  let T := (T0.transHomeomorph H).transHomeomorph J
  have hTs : T.source = T0.source := rfl
  have hheight (y : frontier N) (hy : y ∈ T.source) :
      (T y).2 = -lambda (G y) := by
    change (J (r (T0 y))).2 = _
    rw [hJ]
    change -lambda (a (r (T0 y))) = _
    rw [har (T0 y).property, hT0 y hy]
  have hzero (y : frontier N) (hy : y ∈ T.source) : psi (G y) = 0 := by
    have hyG : (y : X) ∈ G.source := by simpa only [hTs, hT0s, mem_preimage] using hy
    exact (himage.apply_mem_iff hyG).mpr y.property
  have hphase (y : frontier N) (hy : y ∈ T.source) : (y : X) ∈ S ↔ 0 ≤ (T y).2 := by
    have hyG : (y : X) ∈ G.source := by simpa only [hTs, hT0s, mem_preimage] using hy
    rw [hS y hyG, hzero y hy, hheight y hy]
    simp only [true_and, neg_nonneg]
  have hold (y : frontier N) (hy : y ∈ T.source) : (y : X) ∈ O ↔ (T y).2 ≤ 0 := by
    have hyG : (y : X) ∈ G.source := by simpa only [hTs, hT0s, mem_preimage] using hy
    rw [hO y hyG, hzero y hy, hheight y hy]
    simp only [true_and, neg_nonpos]
  refine ⟨T, ?_, hphase, hold, ?_⟩
  · simpa only [hTs, hT0s, mem_preimage] using hx
  · intro y hy
    change ((y : X) ∈ S ∧ (y : X) ∈ O) ↔ _
    rw [hphase y hy, hold y hy]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
