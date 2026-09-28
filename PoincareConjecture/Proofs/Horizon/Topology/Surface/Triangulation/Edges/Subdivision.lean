import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

private theorem subinterval_parameter_mem {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc (0 : ℝ) 1) :
    a + t * (b - a) ∈ Icc a b := by
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]

noncomputable def SmoothEdge.subedge (e : SmoothEdge M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : SmoothEdge M where
  map t := e.map (a + t * (b - a))
  smooth := e.smooth.comp
    (contDiff_const.add (contDiff_id.mul contDiff_const)).contMDiff.contMDiffOn
    (fun t ht => Icc_subset_Icc ha hb (subinterval_parameter_mem hab.le ht))
  regular := by
    intro t ht
    have hinner : a + t * (b - a) ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> nlinarith [mul_pos ht.1 (sub_pos.mpr hab),
        mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hab)]
    have hd : HasFDerivAt (fun s : ℝ => a + s * (b - a))
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (b - a)) t := by
      convert! ((hasFDerivAt_id t).smul_const (b - a)).const_add a using 1
    change Function.Injective
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) (e.map ∘ fun s => a + s * (b - a)) t)
    rw [mfderiv_comp t
      ((e.smooth.mdifferentiableOn (by simp)).mdifferentiableAt
        (Icc_mem_nhds hinner.1 hinner.2)) hd.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, hd.fderiv]
    exact (e.regular _ hinner).comp (smul_left_injective ℝ (sub_ne_zero.mpr hab.ne'))

@[simp]
theorem SmoothEdge.subedge_map_zero (e : SmoothEdge M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (e.subedge ha hab hb).map 0 = e.map a := by
  simp [SmoothEdge.subedge]

@[simp]
theorem SmoothEdge.subedge_map_one (e : SmoothEdge M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (e.subedge ha hab hb).map 1 = e.map b := by
  simp [SmoothEdge.subedge]

theorem SmoothEdge.subedge_image (e : SmoothEdge M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (e.subedge ha hab hb).map '' Icc (0 : ℝ) 1 = e.map '' Icc a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, subinterval_parameter_mem hab.le ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t - a) / (b - a), ?_, ?_⟩
    · exact ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le),
        (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩
    · change e.map (a + (t - a) / (b - a) * (b - a)) = e.map t
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
      congr 1
      ring

theorem SmoothEdge.subedge_injOn (e : SmoothEdge M)
    (he : InjOn e.map (Icc (0 : ℝ) 1)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    InjOn (e.subedge ha hab hb).map (Icc (0 : ℝ) 1) := by
  intro s hs t ht h
  have hp := he (Icc_subset_Icc ha hb (subinterval_parameter_mem hab.le hs))
    (Icc_subset_Icc ha hb (subinterval_parameter_mem hab.le ht)) h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hab.ne') (add_left_cancel hp)

theorem exists_ordered_unitInterval_cuts (s : Finset ℝ)
    (hs : ∀ t ∈ s, t ∈ Icc (0 : ℝ) 1) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ), 0 < n ∧ StrictMono c ∧
      c 0 = 0 ∧ c (Fin.last n) = 1 ∧
      range c = (↑s : Set ℝ) ∪ {0, 1} := by
  classical
  let cuts := insert 0 (insert 1 s)
  have hzero : (0 : ℝ) ∈ cuts := by simp [cuts]
  have hone : (1 : ℝ) ∈ cuts := by simp [cuts]
  have hcard : 2 ≤ cuts.card := Finset.one_lt_card.mpr ⟨0, hzero, 1, hone, by norm_num⟩
  let n := cuts.card - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hcard' : cuts.card = n + 1 := by dsimp [n]; omega
  let c : Fin (n + 1) ↪o ℝ := cuts.orderEmbOfFin hcard'
  have hmem (i : Fin (n + 1)) : c i ∈ cuts := cuts.orderEmbOfFin_mem hcard' i
  have hbounds : ∀ t ∈ cuts, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    simp only [cuts, Finset.mem_insert] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hs t ht
  have hrange : range c = (↑cuts : Set ℝ) := cuts.range_orderEmbOfFin hcard'
  refine ⟨n, c, hn, c.strictMono, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, c i = 0 := by rw [← mem_range, hrange]; exact hzero
    exact le_antisymm (hi ▸ c.monotone (Fin.zero_le i)) (hbounds _ (hmem 0)).1
  · obtain ⟨i, hi⟩ : ∃ i, c i = 1 := by rw [← mem_range, hrange]; exact hone
    exact le_antisymm (hbounds _ (hmem (Fin.last n))).2
      (hi ▸ c.monotone (Fin.le_last i))
  · rw [hrange]
    ext t
    simp only [cuts, Finset.mem_coe, Finset.mem_insert, mem_union, mem_insert_iff,
      mem_singleton_iff]
    tauto

theorem iUnion_Icc_consecutive {n : ℕ} (hn : 0 < n)
    (c : Fin (n + 1) → ℝ) (hc : Monotone c) :
    (⋃ i : Fin n, Icc (c i.castSucc) (c i.succ)) = Icc (c 0) (c (Fin.last n)) := by
  classical
  apply Subset.antisymm
  · intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨(hc (Fin.zero_le _)).trans hi.1, hi.2.trans (hc (Fin.le_last _))⟩
  · intro t ht
    let s := Finset.univ.filter (fun i : Fin (n + 1) => c i ≤ t)
    have hs : s.Nonempty := ⟨0, by simp [s, ht.1]⟩
    let j := s.max' hs
    have hj : c j ≤ t := (Finset.mem_filter.mp (s.max'_mem hs)).2
    by_cases hlast : j = Fin.last n
    · let i : Fin n := ⟨n - 1, by omega⟩
      have hi : i.succ = Fin.last n := by ext; dsimp [i]; omega
      apply mem_iUnion.mpr
      refine ⟨i, ?_, ?_⟩
      · exact (hc (Fin.castSucc_le_succ i)).trans (hi ▸ hlast ▸ hj)
      · simpa only [hi] using ht.2
    · have hjlt : j.val < n := by
        have hjle := j.isLt
        have hjne : j.val ≠ n := fun h => hlast (Fin.ext h)
        omega
      let i : Fin n := ⟨j.val, hjlt⟩
      have hi : i.castSucc = j := by ext; rfl
      apply mem_iUnion.mpr
      refine ⟨i, hi ▸ hj, ?_⟩
      by_contra h
      have hsucc : i.succ ∈ s := by simp [s, (not_le.mp h).le]
      have hle := s.le_max' i.succ hsucc
      have hlt : j < i.succ := hi ▸ (Fin.castSucc_lt_succ (i := i))
      exact (not_lt_of_ge hle) hlt

theorem SmoothEdge.exists_finite_subdivision (e : SmoothEdge M)
    (he : InjOn e.map (Icc (0 : ℝ) 1)) (s : Finset ℝ)
    (hs : ∀ t ∈ s, t ∈ Icc (0 : ℝ) 1) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ) (piece : Fin n → SmoothEdge M),
      0 < n ∧ StrictMono c ∧ c 0 = 0 ∧ c (Fin.last n) = 1 ∧
      range c = (↑s : Set ℝ) ∪ {0, 1} ∧
      (∀ i t, (piece i).map t = e.map (c i.castSucc + t * (c i.succ - c i.castSucc))) ∧
      (∀ i, InjOn (piece i).map (Icc (0 : ℝ) 1)) ∧
      (⋃ i, (piece i).map '' Icc (0 : ℝ) 1) = e.map '' Icc (0 : ℝ) 1 ∧
      (∀ i j, i < j → (piece i).map '' Icc (0 : ℝ) 1 ∩
        (piece j).map '' Icc (0 : ℝ) 1 ⊆ {e.map (c i.succ)}) ∧
      (∀ i, Disjoint ((piece i).map '' Ioo (0 : ℝ) 1) (e.map '' range c)) := by
  obtain ⟨n, c, hn, hc, hzero, hone, hrange⟩ := exists_ordered_unitInterval_cuts s hs
  have hbounds (i : Fin (n + 1)) : c i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hzero] using hc.monotone (Fin.zero_le i)
    · simpa only [hone] using hc.monotone (Fin.le_last i)
  have hinc (i : Fin n) : c i.castSucc < c i.succ := hc Fin.castSucc_lt_succ
  let piece (i : Fin n) := e.subedge (hbounds i.castSucc).1 (hinc i) (hbounds i.succ).2
  have himage (i : Fin n) : (piece i).map '' Icc (0 : ℝ) 1 =
      e.map '' Icc (c i.castSucc) (c i.succ) := e.subedge_image _ _ _
  have hsub (i : Fin n) : Icc (c i.castSucc) (c i.succ) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hbounds i.castSucc).1 (hbounds i.succ).2
  refine ⟨n, c, piece, hn, hc, hzero, hone, hrange, fun _ _ => rfl,
    fun i => e.subedge_injOn he _ _ _, ?_, ?_, ?_⟩
  · simp_rw [himage]
    rw [← image_iUnion, iUnion_Icc_consecutive hn c hc.monotone, hzero, hone]
  · intro i j hij x hx
    rw [himage i, himage j] at hx
    obtain ⟨a, ha, rfl⟩ := hx.1
    obtain ⟨b, hb, hab⟩ := hx.2
    have heq : b = a := he (hsub j hb) (hsub i ha) hab
    have horder : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have ha' : c i.succ ≤ a := (hc.monotone horder).trans (heq ▸ hb.1)
    exact congrArg e.map (le_antisymm ha.2 ha')
  · intro i
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ ⟨a, ⟨k, rfl⟩, heq⟩
    have ht' : c i.castSucc + t * (c i.succ - c i.castSucc) ∈
        Ioo (c i.castSucc) (c i.succ) := by
      constructor <;> nlinarith [mul_pos ht.1 (sub_pos.mpr (hinc i)),
        mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr (hinc i))]
    have heq' : c k = c i.castSucc + t * (c i.succ - c i.castSucc) :=
      he (hbounds k) (hsub i ⟨ht'.1.le, ht'.2.le⟩) heq
    have hleft : i.castSucc < k := hc.lt_iff_lt.mp (heq' ▸ ht'.1)
    have hright : k < i.succ := hc.lt_iff_lt.mp (heq' ▸ ht'.2)
    have hl : i.val < k.val := hleft
    have hr : k.val < i.val + 1 := hright
    omega

end PoincareConjecture.Topology.Surface
