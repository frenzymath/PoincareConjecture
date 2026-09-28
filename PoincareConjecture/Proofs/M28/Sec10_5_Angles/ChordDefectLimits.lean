import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Prod
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M28

def chordDefect (d : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  (d s t ^ 2 - (s - t) ^ 2) / (s * t)

private theorem positive_Ioc_mem_nhdsGT {a : ℝ} (ha : 0 < a) :
    Ioc (0 : ℝ) a ∈ 𝓝[>] (0 : ℝ) := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ha)] with s hs hsa
  exact ⟨hs, hsa⟩

theorem chordDefect_bounds {d : ℝ → ℝ → ℝ} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hlower : |s - t| ≤ d s t)
    (hupper : d s t ≤ s + t) :
    chordDefect d s t ∈ Icc (0 : ℝ) 4 := by
  have hd : 0 ≤ d s t := (abs_nonneg _).trans hlower
  have hlowerSq : (s - t) ^ 2 ≤ d s t ^ 2 := by
    have hh := mul_le_mul hlower hlower (abs_nonneg _) hd
    simpa only [← pow_two, sq_abs] using hh
  have hupperSq : d s t ^ 2 ≤ (s + t) ^ 2 := by
    have hh := mul_le_mul hupper hupper hd (by linarith : 0 ≤ s + t)
    simpa only [← pow_two] using hh
  refine ⟨div_nonneg (sub_nonneg.mpr hlowerSq) (mul_pos hs ht).le, ?_⟩
  change (d s t ^ 2 - (s - t) ^ 2) / (s * t) ≤ 4
  apply (div_le_iff₀ (mul_pos hs ht)).mpr
  nlinarith

theorem chordDefect_le_of_corresponding_side_lower
    {d : ℝ → ℝ → ℝ} {S T s t : ℝ}
    (hS : 0 < S) (hT : 0 < T) (hs : 0 < s) (ht : 0 < t)
    (hcomparison : d s t ^ 2 ≥ s ^ 2 + t ^ 2 -
      2 * s * t * ((S ^ 2 + T ^ 2 - d S T ^ 2) / (2 * S * T))) :
    chordDefect d S T ≤ chordDefect d s t := by
  have hidentity :
      s ^ 2 + t ^ 2 - 2 * s * t *
          ((S ^ 2 + T ^ 2 - d S T ^ 2) / (2 * S * T)) =
        (s - t) ^ 2 + s * t * chordDefect d S T := by
    unfold chordDefect
    field_simp [hS.ne', hT.ne']
    ring
  rw [hidentity] at hcomparison
  change chordDefect d S T ≤ (d s t ^ 2 - (s - t) ^ 2) / (s * t)
  apply (le_div_iff₀ (mul_pos hs ht)).mpr
  nlinarith

theorem exists_joint_chord_limit
    {k : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) B,
      k s t ∈ Icc (0 : ℝ) 4)
    (hmono : ∀ S ∈ Ioc (0 : ℝ) A, ∀ T ∈ Ioc (0 : ℝ) B,
      ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) T, k S T ≤ k s t) :
    ∃ K : ℝ, K ∈ Icc (0 : ℝ) 4 ∧
      (∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) B, k s t ≤ K) ∧
      Tendsto (fun p : ℝ × ℝ => k p.1 p.2)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K) := by
  let V : Set ℝ := {z | ∃ s ∈ Ioc (0 : ℝ) A, ∃ t ∈ Ioc (0 : ℝ) B, k s t = z}
  have hVnonempty : V.Nonempty := ⟨k A B, A, ⟨hA, le_rfl⟩, B, ⟨hB, le_rfl⟩, rfl⟩
  have hVbound : BddAbove V := by
    refine ⟨4, ?_⟩
    rintro z ⟨s, hs, t, ht, rfl⟩
    exact (hbound s hs t ht).2
  let K : ℝ := sSup V
  have hupper (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) A)
      (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) B) : k s t ≤ K :=
    le_csSup hVbound ⟨s, hs, t, ht, rfl⟩
  have hKbound : K ∈ Icc (0 : ℝ) 4 := by
    constructor
    · exact ((hbound A ⟨hA, le_rfl⟩ B ⟨hB, le_rfl⟩).1).trans
        (hupper A ⟨hA, le_rfl⟩ B ⟨hB, le_rfl⟩)
    · apply csSup_le hVnonempty
      rintro z ⟨s, hs, t, ht, rfl⟩
      exact (hbound s hs t ht).2
  refine ⟨K, hKbound, hupper, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro l hl
    obtain ⟨z, ⟨S, hS, T, hT, rfl⟩, hz⟩ :=
      exists_lt_of_lt_csSup hVnonempty hl
    filter_upwards [prod_mem_prod (positive_Ioc_mem_nhdsGT hS.1)
      (positive_Ioc_mem_nhdsGT hT.1)] with p hp
    exact hz.trans_le (hmono S hS T hT p.1 hp.1 p.2 hp.2)
  · intro u hu
    filter_upwards [prod_mem_prod (positive_Ioc_mem_nhdsGT hA)
      (positive_Ioc_mem_nhdsGT hB)] with p hp
    exact (hupper p.1 hp.1 p.2 hp.2).trans_lt hu

theorem exists_chordDefect_limit_of_corresponding_side_lower
    {d : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (htriangle : ∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) B,
      |s - t| ≤ d s t ∧ d s t ≤ s + t)
    (hcomparison : ∀ S ∈ Ioc (0 : ℝ) A, ∀ T ∈ Ioc (0 : ℝ) B,
      ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) T,
        d s t ^ 2 ≥ s ^ 2 + t ^ 2 -
          2 * s * t * ((S ^ 2 + T ^ 2 - d S T ^ 2) / (2 * S * T))) :
    ∃ K : ℝ, K ∈ Icc (0 : ℝ) 4 ∧
      (∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) B, chordDefect d s t ≤ K) ∧
      Tendsto (fun p : ℝ × ℝ => chordDefect d p.1 p.2)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K) := by
  apply exists_joint_chord_limit hA hB
  · intro s hs t ht
    exact chordDefect_bounds hs.1 ht.1 (htriangle s hs t ht).1 (htriangle s hs t ht).2
  · intro S hS T hT s hs t ht
    exact chordDefect_le_of_corresponding_side_lower hS.1 hT.1 hs.1 ht.1
      (hcomparison S hS T hT s hs t ht)

theorem chordDefect_le_joint_limit_of_corresponding_side_lower
    {d : ℝ → ℝ → ℝ} {K S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hlimit : Tendsto (fun p : ℝ × ℝ => chordDefect d p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K))
    (hcomparison : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) T,
      d s t ^ 2 ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((S ^ 2 + T ^ 2 - d S T ^ 2) / (2 * S * T))) :
    chordDefect d S T ≤ K := by
  apply ge_of_tendsto hlimit
  filter_upwards [prod_mem_prod (positive_Ioc_mem_nhdsGT hS)
    (positive_Ioc_mem_nhdsGT hT)] with p hp
  exact chordDefect_le_of_corresponding_side_lower hS hT hp.1.1 hp.2.1
    (hcomparison p.1 hp.1 p.2 hp.2)

theorem sqrt_chord_limit_bounds {K : ℝ} (hK : K ∈ Icc (0 : ℝ) 4) :
    Real.sqrt K ∈ Icc (0 : ℝ) 2 ∧ (Real.sqrt K) ^ 2 = K := by
  have hnonneg := Real.sqrt_nonneg K
  have hsquare := Real.sq_sqrt hK.1
  exact ⟨⟨hnonneg, by nlinarith [hK.2]⟩, hsquare⟩

private theorem tendsto_pos_mul_right {r : ℝ} (hr : 0 < r) :
    Tendsto (fun h : ℝ => h * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [zero_mul] using hid.mul_const r
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_pos hh hr

private theorem scaled_chordDefect_identity (d : ℝ → ℝ → ℝ)
    {h r s : ℝ} (hh : h ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    (d (h * r) (h * s) / h) ^ 2 =
      (r - s) ^ 2 + r * s * chordDefect d (h * r) (h * s) := by
  unfold chordDefect
  field_simp [hh, hr, hs]
  ring

private theorem sqrt_scaled_chordDefect_identity (d : ℝ → ℝ → ℝ)
    {h r s : ℝ} (hh : 0 < h) (hr : 0 < r) (hs : 0 < s)
    (hd : 0 ≤ d (h * r) (h * s)) :
    Real.sqrt ((r - s) ^ 2 + r * s * chordDefect d (h * r) (h * s)) =
      d (h * r) (h * s) / h := by
  rw [← scaled_chordDefect_identity d hh.ne' hr.ne' hs.ne']
  exact Real.sqrt_sq (div_nonneg hd hh.le)

theorem tendsto_rescaled_distance_of_chordDefect_limit
    {d : ℝ → ℝ → ℝ} {A B K r s : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hs : 0 < s)
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) A, ∀ y ∈ Ioc (0 : ℝ) B, 0 ≤ d x y)
    (hlimit : Tendsto (fun p : ℝ × ℝ => chordDefect d p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K)) :
    Tendsto (fun h : ℝ => d (h * r) (h * s) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt ((r - s) ^ 2 + r * s * K))) := by
  have hrmap := tendsto_pos_mul_right hr
  have hsmap := tendsto_pos_mul_right hs
  have hpair : Tendsto (fun h : ℝ => (h * r, h * s))
      (𝓝[>] (0 : ℝ)) ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) :=
    hrmap.prodMk hsmap
  have hk : Tendsto (fun h : ℝ => chordDefect d (h * r) (h * s))
      (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [Function.comp_def] using hlimit.comp hpair
  have hquadratic :
      Tendsto (fun h : ℝ => (r - s) ^ 2 + r * s * chordDefect d (h * r) (h * s))
        (𝓝[>] (0 : ℝ)) (𝓝 ((r - s) ^ 2 + r * s * K)) :=
    (tendsto_const_nhds (x := (r - s) ^ 2)).add
      ((tendsto_const_nhds (x := r * s)).mul hk)
  have hroot :
      Tendsto (fun h : ℝ => Real.sqrt ((r - s) ^ 2 +
        r * s * chordDefect d (h * r) (h * s)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt ((r - s) ^ 2 + r * s * K))) :=
    hquadratic.sqrt
  have heq :
      (fun h : ℝ => Real.sqrt ((r - s) ^ 2 +
        r * s * chordDefect d (h * r) (h * s))) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun h : ℝ => d (h * r) (h * s) / h) := by
    filter_upwards [self_mem_nhdsWithin,
      hrmap.eventually (positive_Ioc_mem_nhdsGT hA),
      hsmap.eventually (positive_Ioc_mem_nhdsGT hB)] with h hh hhr hhs
    exact sqrt_scaled_chordDefect_identity d hh hr hs (hnonneg _ hhr _ hhs)
  exact Filter.Tendsto.congr' heq hroot

theorem tendsto_equal_radius_distance_of_chordDefect_limit
    {d : ℝ → ℝ → ℝ} {A B K : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) A, ∀ y ∈ Ioc (0 : ℝ) B, 0 ≤ d x y)
    (hlimit : Tendsto (fun p : ℝ × ℝ => chordDefect d p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 K)) :
    Tendsto (fun h : ℝ => d h h / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt K)) := by
  simpa only [mul_one, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    one_mul, zero_add] using
    tendsto_rescaled_distance_of_chordDefect_limit hA hB
      (r := 1) (s := 1) zero_lt_one zero_lt_one hnonneg hlimit

end PoincareConjecture.M28
