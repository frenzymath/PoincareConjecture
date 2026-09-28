import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_end_height_clamp (a b d : ℝ)
    (hab : a < b) (hd : 0 < d) :
    ∃ k : ℝ → ℝ, ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc (a - d) (b + d)) ∧
      EqOn k id (Icc a b) := by
  let m := (a + b) / 2
  let r := (b - a) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let chi : ContDiffBump m := ⟨r, r + d / 2, hr, by linarith⟩
  let k : ℝ → ℝ := fun z => m + (z - m) * chi z
  have hk : ContDiff ℝ ∞ k :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).mul chi.contDiff)
  refine ⟨k, hk, ?_, ?_⟩
  · intro z
    have hm : m - r = a ∧ m + r = b := by dsimp [m, r]; constructor <;> ring
    by_cases hz : z ∈ ball m chi.rOut
    · have hdist : |z - m| < r + d / 2 := by
        simpa only [mem_ball, Real.dist_eq] using hz
      have hnonneg : 0 ≤ chi z := chi.nonneg
      have hone : chi z ≤ 1 := chi.le_one
      have hmul : |(z - m) * chi z| ≤ |z - m| := by
        rw [abs_mul, abs_of_nonneg hnonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) hone
      have hbound := abs_le.mp hmul
      dsimp only [k]
      constructor <;> linarith [hm.1, hm.2]
    · have hzero : chi z = 0 := chi.zero_of_le_dist (not_lt.mp hz)
      dsimp only [k]
      rw [hzero, mul_zero, add_zero]
      constructor <;> dsimp [m] <;> linarith
  · intro z hz
    have hball : z ∈ closedBall m chi.rIn := by
      rw [mem_closedBall, Real.dist_eq, abs_le]
      change -r ≤ z - m ∧ z - m ≤ r
      dsimp [m, r]
      constructor <;> linarith [hz.1, hz.2]
    dsimp only [k, id_eq]
    rw [chi.one_of_mem_closedBall hball, mul_one]
    ring

theorem exists_saddle_end_circle_buffer
    (U : Set (UnitCircle × ℝ)) (hU : IsOpen U)
    (a b : ℝ) (hab : a ≤ b)
    (hsub : (univ : Set UnitCircle) ×ˢ Icc a b ⊆ U) :
    ∃ d : ℝ, 0 < d ∧ (univ : Set UnitCircle) ×ˢ Icc (a - d) (b + d) ⊆ U := by
  have hK : IsCompact ((univ : Set UnitCircle) ×ˢ Icc a b) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨d, hd, hthick⟩ := hK.exists_thickening_subset_open hU hsub
  refine ⟨d / 2, by positivity, ?_⟩
  rintro ⟨q, z⟩ ⟨_, hz⟩
  apply hthick
  apply mem_thickening_iff.mpr
  by_cases hza : z < a
  · refine ⟨(q, a), ⟨mem_univ _, le_rfl, hab⟩, ?_⟩
    rw [dist_prod_same_left, Real.dist_eq, abs_of_neg (sub_neg.mpr hza)]
    linarith [hz.1]
  · by_cases hbz : b < z
    · refine ⟨(q, b), ⟨mem_univ _, hab, le_rfl⟩, ?_⟩
      rw [dist_prod_same_left, Real.dist_eq, abs_of_pos (sub_pos.mpr hbz)]
      linarith [hz.2]
    · exact ⟨(q, z), ⟨mem_univ _, le_of_not_gt hza, le_of_not_gt hbz⟩,
        by simpa only [dist_self] using hd⟩

theorem exists_saddle_end_disc_buffer (K : Set ℝ) (hK : IsCompact K)
    (U : Set (E2 × ℝ)) (hU : IsOpen U)
    (hsub : closedBall (0 : E2) 1 ×ˢ K ⊆ U) :
    ∃ r : ℝ, 1 < r ∧ ball (0 : E2) r ×ˢ K ⊆ U := by
  obtain ⟨V, J, hV, _, hball, hKJ, hVJ⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : E2) 1) hK hU hsub
  obtain ⟨d, hd, hdV⟩ :=
    (isCompact_closedBall (0 : E2) 1).exists_thickening_subset_open hV hball
  rw [thickening_closedBall hd zero_le_one] at hdV
  exact ⟨d + 1, by linarith, (prod_mono hdV hKJ).trans hVJ⟩

theorem exists_saddle_end_chart_reparam
    (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (heh : ∀ p ∈ e.source, (e p).2 = p.2)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) :
    ∃ f : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ),
      (∀ p, f p = ((e (p.1, k p.2)).1, p.2)) ∧
      (∀ p, f.symm p = ((e.symm (p.1, k p.2)).1, p.2)) ∧
      f.source = {p | (p.1, k p.2) ∈ e.source} ∧
      f.target = {p | (p.1, k p.2) ∈ e.target} ∧
      ContDiffOn ℝ ∞ f f.source ∧
      ContDiffOn ℝ ∞ f.symm f.target ∧
      (∀ p, (f p).2 = p.2) := by
  let A : E2 × ℝ → E2 × ℝ := fun p => (p.1, k p.2)
  let S : Set (E2 × ℝ) := A ⁻¹' e.source
  let V : Set (E2 × ℝ) := A ⁻¹' e.target
  let f0 : E2 × ℝ → E2 × ℝ := fun p => ((e (A p)).1, p.2)
  let g0 : E2 × ℝ → E2 × ℝ := fun p => ((e.symm (A p)).1, p.2)
  have hA : ContDiff ℝ ∞ A := contDiff_fst.prodMk (hk.comp contDiff_snd)
  have hS : IsOpen S := e.open_source.preimage hA.continuous
  have hV : IsOpen V := e.open_target.preimage hA.continuous
  have hinvh (p : E2 × ℝ) (hp : p ∈ e.target) : (e.symm p).2 = p.2 := by
    have h := heh (e.symm p) (e.map_target hp)
    rw [e.right_inv hp] at h
    exact h.symm
  have hAf (p : E2 × ℝ) (hp : p ∈ S) : A (f0 p) = e (A p) := by
    apply Prod.ext
    · rfl
    · exact (heh (A p) hp).symm
  have hAg (p : E2 × ℝ) (hp : p ∈ V) : A (g0 p) = e.symm (A p) := by
    apply Prod.ext
    · rfl
    · exact (hinvh (A p) hp).symm
  have hmapf (p : E2 × ℝ) (hp : p ∈ S) : f0 p ∈ V := by
    change A (f0 p) ∈ e.target
    rw [hAf p hp]
    exact e.map_source hp
  have hmapg (p : E2 × ℝ) (hp : p ∈ V) : g0 p ∈ S := by
    change A (g0 p) ∈ e.source
    rw [hAg p hp]
    exact e.map_target hp
  have hgf (p : E2 × ℝ) (hp : p ∈ S) : g0 (f0 p) = p := by
    apply Prod.ext
    · change (e.symm (A (f0 p))).1 = p.1
      rw [hAf p hp, e.left_inv hp]
    · rfl
  have hfg (p : E2 × ℝ) (hp : p ∈ V) : f0 (g0 p) = p := by
    apply Prod.ext
    · change (e (A (g0 p))).1 = p.1
      rw [hAg p hp, e.right_inv hp]
    · rfl
  have hf : ContDiffOn ℝ ∞ f0 S :=
    ((he.comp hA.contDiffOn (fun _ hp => hp)).fst).prodMk contDiff_snd.contDiffOn
  have hg : ContDiffOn ℝ ∞ g0 V :=
    ((hei.comp hA.contDiffOn (fun _ hp => hp)).fst).prodMk contDiff_snd.contDiffOn
  let f : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ) := {
    toFun := f0
    invFun := g0
    source := S
    target := V
    map_source' := hmapf
    map_target' := hmapg
    left_inv' := hgf
    right_inv' := hfg
    open_source := hS
    open_target := hV
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn }
  exact ⟨f, fun _ => rfl, fun _ => rfl, rfl, rfl, hf, hg, fun _ => rfl⟩

theorem exists_saddle_end_fiber_chart
    (e : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (heh : ∀ p ∈ e.source, (e p).2 = p.2)
    (z : ℝ) (hdisc : ∀ x ∈ closedBall (0 : E2) 1, (x, z) ∈ e.source) :
    ∃ B : BallNeighborhoodChart E2 E2,
      (∀ x, B.chart x = (e (x, z)).1) ∧
      (∀ y, B.chart.symm y = (e.symm (y, z)).1) ∧
      B.chart.source = {x | (x, z) ∈ e.source} ∧
      B.chart.target = {y | (y, z) ∈ e.target} := by
  let A : E2 → E2 × ℝ := fun x => (x, z)
  let S := A ⁻¹' e.source
  let V := A ⁻¹' e.target
  let f : E2 → E2 := fun x => (e (A x)).1
  let g : E2 → E2 := fun y => (e.symm (A y)).1
  have hA : ContDiff ℝ ∞ A := contDiff_id.prodMk contDiff_const
  have hinvh (p : E2 × ℝ) (hp : p ∈ e.target) : (e.symm p).2 = p.2 := by
    have h := heh (e.symm p) (e.map_target hp)
    rw [e.right_inv hp] at h
    exact h.symm
  have hAf (x : E2) (hx : x ∈ S) : A (f x) = e (A x) := by
    apply Prod.ext
    · rfl
    · exact (heh (A x) hx).symm
  have hAg (y : E2) (hy : y ∈ V) : A (g y) = e.symm (A y) := by
    apply Prod.ext
    · rfl
    · exact (hinvh (A y) hy).symm
  have hf : ContDiffOn ℝ ∞ f S :=
    (he.comp hA.contDiffOn (fun _ hx => hx)).fst
  have hg : ContDiffOn ℝ ∞ g V :=
    (hei.comp hA.contDiffOn (fun _ hy => hy)).fst
  let chart : OpenPartialHomeomorph E2 E2 := {
    toFun := f
    invFun := g
    source := S
    target := V
    map_source' := by
      intro x hx
      change A (f x) ∈ e.target
      rw [hAf x hx]
      exact e.map_source hx
    map_target' := by
      intro y hy
      change A (g y) ∈ e.source
      rw [hAg y hy]
      exact e.map_target hy
    left_inv' := by
      intro x hx
      change (e.symm (A (f x))).1 = x
      rw [hAf x hx, e.left_inv hx]
    right_inv' := by
      intro y hy
      change (e (A (g y))).1 = y
      rw [hAg y hy, e.right_inv hy]
    open_source := e.open_source.preimage hA.continuous
    open_target := e.open_target.preimage hA.continuous
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn }
  exact ⟨⟨chart, hdisc, hf, hg⟩, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem exists_saddle_end_common_circles
    (Q R : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (h : UnitTwoSphere → ℝ) (ell : ℝ)
    (hQ : ∀ p ∈ Q.source, h (Q p) = p.2)
    (hR : ∀ p ∈ R.source, h (R p) = p.2)
    (hQs : ∀ q : UnitCircle, (q, ell) ∈ Q.source)
    (hRs : ∀ q : UnitCircle, (q, ell) ∈ R.source)
    (hbottom : range (fun q : UnitCircle => Q (q, ell)) =
      range (fun q : UnitCircle => R (q, ell))) :
    ∃ d : ℝ, 0 < d ∧
      ((univ : Set UnitCircle) ×ˢ Icc (ell - d) (ell + d) ⊆ Q.source) ∧
      ((univ : Set UnitCircle) ×ˢ Icc (ell - d) (ell + d) ⊆ R.source) ∧
      ∀ z ∈ Icc (ell - d) (ell + d),
        range (fun q : UnitCircle => Q (q, z)) =
          range (fun q : UnitCircle => R (q, z)) := by
  let U := Q.source ∩ Q ⁻¹' R.target
  let V := R.source ∩ R ⁻¹' Q.target
  have hU : IsOpen U := Q.isOpen_inter_preimage R.open_target
  have hV : IsOpen V := R.isOpen_inter_preimage Q.open_target
  have hU0 : (univ : Set UnitCircle) ×ˢ Icc ell ell ⊆ U := by
    rintro ⟨q, z⟩ ⟨_, hz⟩
    have hz0 : z = ell := le_antisymm hz.2 hz.1
    subst z
    refine ⟨hQs q, ?_⟩
    have hm : Q (q, ell) ∈ range (fun q : UnitCircle => R (q, ell)) := by
      rw [← hbottom]
      exact mem_range_self q
    rcases hm with ⟨r, hr⟩
    change Q (q, ell) ∈ R.target
    rw [← hr]
    exact R.map_source (hRs r)
  have hV0 : (univ : Set UnitCircle) ×ˢ Icc ell ell ⊆ V := by
    rintro ⟨q, z⟩ ⟨_, hz⟩
    have hz0 : z = ell := le_antisymm hz.2 hz.1
    subst z
    refine ⟨hRs q, ?_⟩
    have hm : R (q, ell) ∈ range (fun q : UnitCircle => Q (q, ell)) := by
      rw [hbottom]
      exact mem_range_self q
    rcases hm with ⟨r, hr⟩
    change R (q, ell) ∈ Q.target
    rw [← hr]
    exact Q.map_source (hQs r)
  obtain ⟨d1, hd1, h1⟩ := exists_saddle_end_circle_buffer U hU ell ell le_rfl hU0
  obtain ⟨d2, hd2, h2⟩ := exists_saddle_end_circle_buffer V hV ell ell le_rfl hV0
  let d := min d1 d2
  have hd : 0 < d := lt_min hd1 hd2
  have hI1 : Icc (ell - d) (ell + d) ⊆ Icc (ell - d1) (ell + d1) := by
    intro z hz
    constructor <;> linarith [min_le_left d1 d2, hz.1, hz.2]
  have hI2 : Icc (ell - d) (ell + d) ⊆ Icc (ell - d2) (ell + d2) := by
    intro z hz
    constructor <;> linarith [min_le_right d1 d2, hz.1, hz.2]
  have hu (q : UnitCircle) {z : ℝ} (hz : z ∈ Icc (ell - d) (ell + d)) :
      (q, z) ∈ U := h1 ⟨mem_univ _, hI1 hz⟩
  have hv (q : UnitCircle) {z : ℝ} (hz : z ∈ Icc (ell - d) (ell + d)) :
      (q, z) ∈ V := h2 ⟨mem_univ _, hI2 hz⟩
  refine ⟨d, hd, fun p hp => (hu p.1 hp.2).1,
    fun p hp => (hv p.1 hp.2).1, ?_⟩
  intro z hz
  apply Set.Subset.antisymm
  · rintro y ⟨q, rfl⟩
    have hqt := (hu q hz).2
    have hqs := R.map_target hqt
    have hheight : (R.symm (Q (q, z))).2 = z := by
      have hh := hR (R.symm (Q (q, z))) hqs
      rw [R.right_inv hqt, hQ (q, z) (hu q hz).1] at hh
      exact hh.symm
    refine ⟨(R.symm (Q (q, z))).1, ?_⟩
    change R ((R.symm (Q (q, z))).1, z) = Q (q, z)
    have heq : ((R.symm (Q (q, z))).1, z) = R.symm (Q (q, z)) := by
      apply Prod.ext
      · rfl
      · exact hheight.symm
    rw [heq, R.right_inv hqt]
  · rintro y ⟨q, rfl⟩
    have hqt := (hv q hz).2
    have hqs := Q.map_target hqt
    have hheight : (Q.symm (R (q, z))).2 = z := by
      have hh := hQ (Q.symm (R (q, z))) hqs
      rw [Q.right_inv hqt, hR (q, z) (hv q hz).1] at hh
      exact hh.symm
    refine ⟨(Q.symm (R (q, z))).1, ?_⟩
    change Q ((Q.symm (R (q, z))).1, z) = R (q, z)
    have heq : ((Q.symm (R (q, z))).1, z) = Q.symm (R (q, z)) := by
      apply Prod.ext
      · rfl
      · exact hheight.symm
    rw [heq, Q.right_inv hqt]

end PoincareConjecture.M25.Topology3D
