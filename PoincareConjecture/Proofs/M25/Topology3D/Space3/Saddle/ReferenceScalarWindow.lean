import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ScalarHeightFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff NNReal Topology Manifold

namespace PoincareConjecture.M25.Topology3D




theorem reference_scalar_window :
    ∀ (lo hi s t k d : ℝ),
      s ∈ Ioo lo hi → t ∈ Ioo lo hi →
      Icc (min s t) (max s t) ⊆ Ioo (k - d) (k + d) →
      ∃ (e : ℝ)
        (g : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
        (C : Set ℝ),
        let a := min s t
        let b := max s t
        let W := Ioo (a - 3 * e) (b + 3 * e)
        0 < e ∧
        Icc (a - 4 * e) (b + 4 * e) ⊆
          Ioo lo hi ∩ Ioo (k - d) (k + d) ∧
        IsCompact C ∧ C ⊆ W ∧
        ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × ℝ => (g q.1).symm q.2) ∧
        (∀ r x : ℝ, (g r).symm x = g (-r) x) ∧
        (∀ x : ℝ, g 0 x = x) ∧
        (∀ r : ℝ, StrictMono (g r) ∧ StrictMono (g r).symm) ∧
        (∀ r : ℝ,
          tsupport (fun x : ℝ => g r x - x) ⊆ C ∧
          tsupport (fun x : ℝ => (g r).symm x - x) ⊆ C) ∧
        (∀ r x : ℝ, x ∉ C →
          g r x = x ∧ (g r).symm x = x) ∧
        (∀ r x : ℝ, x ∉ W →
          g r x = x ∧ (g r).symm x = x) ∧
        (∀ r x : ℝ, x ∉ Ioo (k - d) (k + d) →
          g r x = x ∧ (g r).symm x = x) ∧
        (∀ r x : ℝ,
          (g r x ∈ W ↔ x ∈ W) ∧
          ((g r).symm x ∈ W ↔ x ∈ W)) ∧
        (∀ h : ℝ, |h| ≤ e → ∀ r ∈ Icc (0 : ℝ) 1,
          g r (s + h) = s + h + r * (t - s)) ∧
        (∀ h : ℝ, |h| ≤ e →
          g 1 (s + h) = t + h ∧
          (g 1).symm (t + h) = s + h) := by
  classical
  intro lo hi s t k d hs ht hJ
  let a := min s t
  let b := max s t
  have has : a ≤ s := min_le_left s t
  have hat : a ≤ t := min_le_right s t
  have hsb : s ≤ b := le_max_left s t
  have htb : t ≤ b := le_max_right s t
  have hab : a ≤ b := has.trans hsb
  have hloa : lo < a := lt_min hs.1 ht.1
  have hbhi : b < hi := max_lt hs.2 ht.2
  have haJ : a ∈ Ioo (k - d) (k + d) := hJ ⟨le_rfl, hab⟩
  have hbJ : b ∈ Ioo (k - d) (k + d) := hJ ⟨hab, le_rfl⟩
  let mu := min (a - lo)
    (min (hi - b) (min (a - (k - d)) (k + d - b)))
  have hmu : 0 < mu :=
    lt_min (sub_pos.mpr hloa)
      (lt_min (sub_pos.mpr hbhi)
        (lt_min (sub_pos.mpr haJ.1) (sub_pos.mpr hbJ.2)))
  have hmu0 : mu ≤ a - lo := min_le_left _ _
  have hmu1 : mu ≤ hi - b :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmu2 : mu ≤ a - (k - d) :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hmu3 : mu ≤ k + d - b :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  let e := mu / 8
  have he : 0 < e := div_pos hmu (by norm_num)
  have he8 : 8 * e = mu := by dsimp [e]; ring
  have hleft0 : lo < a - 4 * e := by linarith
  have hright0 : b + 4 * e < hi := by linarith
  have hleftJ : k - d < a - 4 * e := by linarith
  have hrightJ : b + 4 * e < k + d := by linarith
  have hbuffer : Icc (a - 4 * e) (b + 4 * e) ⊆
      Ioo lo hi ∩ Ioo (k - d) (k + d) := by
    intro x hx
    exact ⟨⟨hleft0.trans_le hx.1, hx.2.trans_lt hright0⟩,
      ⟨hleftJ.trans_le hx.1, hx.2.trans_lt hrightJ⟩⟩
  let W := Ioo (a - 3 * e) (b + 3 * e)
  have hWbuffer : W ⊆ Icc (a - 4 * e) (b + 4 * e) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hplateau : Icc (a - 2 * e) (b + 2 * e) ⊆ W := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨rho, hrho, hrhoc, hrhos, hrhonear, _⟩ :=
    exists_compact_smooth_cutoff
      (K := Icc (a - 2 * e) (b + 2 * e)) (U := W)
      isCompact_Icc isOpen_Ioo hplateau
  have hrhoone : EqOn rho (fun _ => (1 : ℝ))
      (Icc (a - 2 * e) (b + 2 * e)) :=
    fun _ hx => subset_of_mem_nhdsSet hrhonear hx
  let v : ℝ → ℝ := fun x => rho x * (t - s)
  have hv : ContDiff ℝ ∞ v := hrho.mul contDiff_const
  have hvc : HasCompactSupport v := by
    change HasCompactSupport (rho * (fun _ : ℝ => t - s))
    exact hrhoc.mul_right
  have hvs : tsupport v ⊆ W :=
    (tsupport_mul_subset_left
      (f := rho) (g := fun _ : ℝ => t - s)).trans hrhos
  have hvplateau (x : ℝ) (hx : x ∈ Icc (a - 2 * e) (b + 2 * e)) :
      v x = t - s := by
    dsimp [v]
    rw [hrhoone hx, one_mul]
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds v hv hvc
  let g : ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    fun r => boundedFlowDiffeomorph v hK hL hv hvc r
  let C := tsupport v
  have hCc : IsCompact C := hvc.isCompact
  have hCW : C ⊆ W := hvs
  have hCJ : C ⊆ Ioo (k - d) (k + d) :=
    fun _ hx => (hbuffer (hWbuffer (hCW hx))).2
  have hflow : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => boundedFlow v hK hL q.1 q.2) :=
    boundedFlow_contDiff v hK hL hv hvc
  have hg : ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2) := by
    change ContDiff ℝ ∞
      (fun q : ℝ × ℝ => boundedFlow v hK hL q.2 q.1)
    exact hflow.comp (contDiff_snd.prodMk contDiff_fst)
  have hgi : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (g q.1).symm q.2) := by
    change ContDiff ℝ ∞
      (fun q : ℝ × ℝ => boundedFlow v hK hL q.2 (-q.1))
    exact hflow.comp (contDiff_snd.prodMk contDiff_fst.neg)
  have hinv (r x : ℝ) : (g r).symm x = g (-r) x := rfl
  have hzero (x : ℝ) : g 0 x = x := boundedFlow_zero v hK hL x
  have hmono (r : ℝ) : StrictMono (g r) :=
    boundedFlow_strictMono v hK hL hv hvc r
  have himono (r : ℝ) : StrictMono (g r).symm :=
    boundedFlow_strictMono v hK hL hv hvc (-r)
  have hsupport (r : ℝ) :
      tsupport (fun x : ℝ => g r x - x) ⊆ C ∧
      tsupport (fun x : ℝ => (g r).symm x - x) ⊆ C := by
    constructor
    · exact closure_mono (boundedFlow_support_subset v hK hL r)
    · exact closure_mono (boundedFlow_support_subset v hK hL (-r))
  have hfixedC (r x : ℝ) (hx : x ∉ C) :
      g r x = x ∧ (g r).symm x = x := by
    have hvx : v x = 0 := image_eq_zero_of_notMem_tsupport hx
    exact ⟨boundedFlow_eq_self v hK hL x hvx r,
      boundedFlow_eq_self v hK hL x hvx (-r)⟩
  have hfixedW (r x : ℝ) (hx : x ∉ W) :
      g r x = x ∧ (g r).symm x = x :=
    hfixedC r x (fun hxc => hx (hCW hxc))
  have hfixedJ (r x : ℝ) (hx : x ∉ Ioo (k - d) (k + d)) :
      g r x = x ∧ (g r).symm x = x :=
    hfixedC r x (fun hxc => hx (hCJ hxc))
  have hleft (r : ℝ) : g r (a - 3 * e) = a - 3 * e :=
    (hfixedW r _ (by simp [W])).1
  have hright (r : ℝ) : g r (b + 3 * e) = b + 3 * e :=
    (hfixedW r _ (by simp [W])).1
  have hmem (r x : ℝ) : g r x ∈ W ↔ x ∈ W := by
    constructor
    · intro hx
      constructor
      · apply (hmono r).lt_iff_lt.mp
        simpa only [hleft r] using hx.1
      · apply (hmono r).lt_iff_lt.mp
        simpa only [hright r] using hx.2
    · intro hx
      constructor
      · simpa only [hleft r] using hmono r hx.1
      · simpa only [hright r] using hmono r hx.2
  have himem (r x : ℝ) : (g r).symm x ∈ W ↔ x ∈ W := by
    change g (-r) x ∈ W ↔ x ∈ W
    exact hmem (-r) x
  have htrack (h : ℝ) (hh : |h| ≤ e) (r : ℝ)
      (hr : r ∈ Icc (0 : ℝ) 1) :
      s + h + r * (t - s) ∈ Icc (a - 2 * e) (b + 2 * e) := by
    have hr0 : 0 ≤ r := hr.1
    have hr1 : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
    have hlower : (1 - r) * a + r * a ≤ (1 - r) * s + r * t :=
      add_le_add (mul_le_mul_of_nonneg_left has hr1)
        (mul_le_mul_of_nonneg_left hat hr0)
    have hupper : (1 - r) * s + r * t ≤ (1 - r) * b + r * b :=
      add_le_add (mul_le_mul_of_nonneg_left hsb hr1)
        (mul_le_mul_of_nonneg_left htb hr0)
    obtain ⟨hhl, hhu⟩ := abs_le.mp hh
    constructor <;> nlinarith
  have hderiv (h : ℝ) (hh : |h| ≤ e) (r : ℝ)
      (hr : r ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun w : ℝ => s + h + w * (t - s))
        (v (s + h + r * (t - s))) r := by
    rw [hvplateau _ (htrack h hh r hr)]
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id r).mul_const (t - s)).const_add (s + h)
  have htrackeq (h : ℝ) (hh : |h| ≤ e) :
      EqOn (boundedFlow v hK hL (s + h))
        (fun r : ℝ => s + h + r * (t - s)) (Icc (0 : ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ x => v x) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
    · exact fun r _ =>
        (boundedFlow_hasDerivAt v hK hL (s + h) r).continuousAt.continuousWithinAt
    · exact fun r _ =>
        (boundedFlow_hasDerivAt v hK hL (s + h) r).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · exact fun r hr => (hderiv h hh r hr).continuousAt.continuousWithinAt
    · exact fun r hr =>
        (hderiv h hh r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · simp only [boundedFlow_zero, zero_mul, add_zero]
  have haff (h : ℝ) (hh : |h| ≤ e) : g 1 (s + h) = t + h := by
    change boundedFlow v hK hL (s + h) 1 = t + h
    calc
      boundedFlow v hK hL (s + h) 1 = s + h + 1 * (t - s) :=
        htrackeq h hh ⟨by norm_num, le_rfl⟩
      _ = t + h := by ring
  have haffinv (h : ℝ) (hh : |h| ≤ e) :
      (g 1).symm (t + h) = s + h := by
    rw [← haff h hh]
    exact (g 1).symm_apply_apply (s + h)
  refine ⟨e, g, C, he, hbuffer, hCc, hCW, hg, hgi, hinv, hzero,
    (fun r => ⟨hmono r, himono r⟩), hsupport, hfixedC, hfixedW,
    hfixedJ, (fun r x => ⟨hmem r x, himem r x⟩), ?_, ?_⟩
  · intro h hh r hr
    exact htrackeq h hh hr
  · exact fun h hh => ⟨haff h hh, haffinv h hh⟩

end PoincareConjecture.M25.Topology3D
