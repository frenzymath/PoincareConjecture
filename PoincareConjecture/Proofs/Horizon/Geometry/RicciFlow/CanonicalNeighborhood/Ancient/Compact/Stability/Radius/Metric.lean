import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.CompactKappaCoreRadius

variable {X : Type*} [MetricSpace X]



theorem closure_ball_eq_of_approximate_split
    (hsplit : ∀ x y : X, ∀ r ε : ℝ, 0 < r → 0 < ε → r < dist x y →
      ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε)
    (p : X) {r : ℝ} (hr : 0 < r) :
    closure (ball p r) = closedBall p r := by
  apply subset_antisymm closure_ball_subset_closedBall
  intro x hx
  by_cases hxr : dist p x < r
  · exact subset_closure (by simpa only [mem_ball, dist_comm] using hxr)
  have heq : dist p x = r := by
    have hle : dist p x ≤ r := by simpa only [mem_closedBall, dist_comm] using hx
    exact le_antisymm hle (le_of_not_gt hxr)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ := min (r / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨z, hpz, hzx⟩ := hsplit p x (r - δ) δ (by linarith) hδ (by rw [heq]; linarith)
  refine ⟨z, ?_, ?_⟩
  · rw [mem_ball, dist_comm, hpz]
    linarith
  · rw [dist_comm]
    rw [heq] at hzx
    linarith

variable [ProperSpace X]



theorem exists_scale_ball
    (hclosure : ∀ p : X, ∀ r : ℝ, 0 < r → closure (ball p r) = closedBall p r)
    (a : X → ℝ) (ha : Continuous a) (hpos : ∀ x, 0 < a x) (p : X) :
    ∃ r : ℝ, 0 < r ∧ (∀ y ∈ ball p r, r ≤ a y) ∧
      ∃ x ∈ closedBall p r, a x = r := by
  let F := fun x ↦ max (dist p x) (a x)
  have hF : Continuous F := (continuous_const.dist continuous_id).max ha
  have hp : p ∈ closedBall p (a p) := mem_closedBall_self (hpos p).le
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall p (a p)).exists_isMinOn ⟨p, hp⟩ hF.continuousOn
  let r := F x
  have hr : 0 < r := (hpos x).trans_le (le_max_right _ _)
  have hrp : r ≤ a p := by
    calc
      r ≤ F p := hmin hp
      _ = a p := by simp only [F, dist_self, max_eq_right (hpos p).le]
  have hminall (y : X) : r ≤ F y := by
    by_cases hy : y ∈ closedBall p (a p)
    · exact hmin hy
    · have hy' : a p < dist p y := by
        simpa only [mem_closedBall, dist_comm, not_le] using hy
      exact hrp.trans (hy'.le.trans (le_max_left _ _))
  have hball (y : X) (hy : y ∈ ball p r) : r ≤ a y := by
    have hyd : dist p y < r := by simpa only [mem_ball, dist_comm] using hy
    by_contra hya
    exact (not_lt_of_ge (hminall y)) (max_lt hyd (lt_of_not_ge hya))
  have hxball : x ∈ closedBall p r := by
    simpa only [mem_closedBall, dist_comm] using (le_max_left (dist p x) (a x))
  have hcl : closure (ball p r) ⊆ {y | r ≤ a y} :=
    closure_minimal hball (isClosed_le continuous_const ha)
  rw [hclosure p r hr] at hcl
  exact ⟨r, hr, hball, x, hxball, le_antisymm (le_max_right _ _) (hcl hxball)⟩


theorem scalar_image_ball_bddAbove {f : X → ℝ} (hf : Continuous f) (p : X) (r : ℝ) :
    BddAbove (f '' ball p r) :=
  ((isCompact_closedBall p r).image hf).bddAbove.mono (image_mono ball_subset_closedBall)



theorem exists_sup_ball_inv_sq_witness
    (hclosure : ∀ p : X, ∀ r : ℝ, 0 < r → closure (ball p r) = closedBall p r)
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) (p : X) :
    ∃ r : ℝ, 0 < r ∧ sSup (f '' ball p r) = r⁻¹ ^ 2 ∧
      ∃ x ∈ closedBall p r, (Real.sqrt (f x))⁻¹ = r := by
  let a := fun x ↦ (Real.sqrt (f x))⁻¹
  have ha : Continuous a := (Real.continuous_sqrt.comp hf).inv₀
    (fun x ↦ (Real.sqrt_pos.mpr (hpos x)).ne')
  have hapos : ∀ x, 0 < a x := fun x ↦ inv_pos.mpr (Real.sqrt_pos.mpr (hpos x))
  obtain ⟨r, hr, hscale, x, hx, hxr⟩ := exists_scale_ball hclosure a ha hapos p
  have hupper (y : X) (hy : y ∈ ball p r) : f y ≤ r⁻¹ ^ 2 := by
    have hsqrt : Real.sqrt (f y) ≤ r⁻¹ := by
      simpa only [a, inv_inv] using inv_anti₀ hr (hscale y hy)
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (f y)) hsqrt 2
    simpa only [Real.sq_sqrt (hpos y).le] using hsq
  have hxval : f x = r⁻¹ ^ 2 := by
    have hsqrt := congrArg Inv.inv hxr
    change ((Real.sqrt (f x))⁻¹)⁻¹ = r⁻¹ at hsqrt
    rw [inv_inv] at hsqrt
    rw [← hsqrt, Real.sq_sqrt (hpos x).le]
  have hne : (f '' ball p r).Nonempty := ⟨f p, mem_image_of_mem f (mem_ball_self hr)⟩
  have hbounded := scalar_image_ball_bddAbove hf p r
  have hsuple : sSup (f '' ball p r) ≤ r⁻¹ ^ 2 := by
    apply csSup_le hne
    rintro _ ⟨y, hy, rfl⟩
    exact hupper y hy
  have hcl : closure (ball p r) ⊆ {y | f y ≤ sSup (f '' ball p r)} :=
    closure_minimal (fun y hy ↦ le_csSup hbounded (mem_image_of_mem f hy))
      (isClosed_le hf continuous_const)
  rw [hclosure p r hr] at hcl
  have heq : sSup (f '' ball p r) = r⁻¹ ^ 2 :=
    le_antisymm hsuple (hxval ▸ hcl hx)
  exact ⟨r, hr, heq, x, hx, hxr⟩



theorem exists_unique_sup_ball_inv_sq
    (hclosure : ∀ p : X, ∀ r : ℝ, 0 < r → closure (ball p r) = closedBall p r)
    (f : X → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x) (p : X) :
    ∃! r : ℝ, 0 < r ∧ sSup (f '' ball p r) = r⁻¹ ^ 2 := by
  obtain ⟨r, hr, heq, _⟩ := exists_sup_ball_inv_sq_witness hclosure f hf hpos p
  refine ⟨r, ⟨hr, heq⟩, ?_⟩
  intro s hs
  have hcompare {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
      (heu : sSup (f '' ball p u) = u⁻¹ ^ 2)
      (hev : sSup (f '' ball p v) = v⁻¹ ^ 2) : u ≤ v → v ≤ u := by
    intro huv
    have hsup : u⁻¹ ^ 2 ≤ v⁻¹ ^ 2 := by
      rw [← heu, ← hev]
      exact csSup_le_csSup (scalar_image_ball_bddAbove hf p v)
        ⟨f p, mem_image_of_mem f (mem_ball_self hu)⟩ (image_mono (ball_subset_ball huv))
    by_contra hvu
    have hlt : u < v := lt_of_not_ge hvu
    have hinv : v⁻¹ < u⁻¹ := inv_strictAnti₀ hu hlt
    have hnonneg : 0 < v⁻¹ := inv_pos.mpr hv
    nlinarith
  rcases le_total s r with hsr | hrs
  · exact le_antisymm hsr (hcompare hs.1 hr hs.2 heq hsr)
  · exact le_antisymm (hcompare hr hs.1 heq hs.2 hrs) hrs

end PoincareConjecture.CompactKappaCoreRadius
