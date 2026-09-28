import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Exterior

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

def movingContact (r t : Real) (j : Fin 2 × Fin 2) : E2 :=
  WithLp.toLp 2 ![
    if j.1 = 0 then Real.sqrt (r ^ 2 - max t 0) else -Real.sqrt (r ^ 2 - max t 0),
    if j.2 = 0 then Real.sqrt (r ^ 2 + min t 0) else -Real.sqrt (r ^ 2 + min t 0)]

theorem continuous_movingContact (r : Real) (j : Fin 2 × Fin 2) :
    Continuous (fun t => movingContact r t j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => Real)).comp
  apply continuous_pi
  intro k
  fin_cases k
  · change Continuous (fun t : Real =>
      if j.1 = 0 then Real.sqrt (r ^ 2 - max t 0) else -Real.sqrt (r ^ 2 - max t 0))
    split_ifs
    · exact (continuous_const.sub (continuous_id.max continuous_const)).sqrt
    · exact (continuous_const.sub (continuous_id.max continuous_const)).sqrt.neg
  · change Continuous (fun t : Real =>
      if j.2 = 0 then Real.sqrt (r ^ 2 + min t 0) else -Real.sqrt (r ^ 2 + min t 0))
    split_ifs
    · exact (continuous_const.add (continuous_id.min continuous_const)).sqrt
    · exact (continuous_const.add (continuous_id.min continuous_const)).sqrt.neg

@[simp] theorem movingContact_zero {r : Real} (hr : 0 < r) (j : Fin 2 × Fin 2) :
    movingContact r 0 j = contact r j := by
  ext k
  fin_cases k <;> simp [movingContact, contact, Real.sqrt_sq_eq_abs, abs_of_pos hr]

theorem movingContact_eq_positive {r t : Real} (hr : 0 < r) (ht : 0 ≤ t)
    (j : Fin 2 × Fin 2) :
    movingContact r t j = positiveLevelContact r t (j.2, Fin.rev j.1) := by
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> ext l <;> fin_cases l <;>
    simp [movingContact, positiveLevelContact, hyperbolaRadius, max_eq_left ht,
      min_eq_right ht, Real.sqrt_sq_eq_abs, abs_of_pos hr, Fin.rev]

theorem movingContact_eq_negative {r t : Real} (hr : 0 < r) (ht : t ≤ 0)
    (j : Fin 2 × Fin 2) :
    movingContact r t j = negativeLevelContact r (-t) (j.1, Fin.rev j.2) := by
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> ext l <;> fin_cases l <;>
    simp [movingContact, negativeLevelContact, positiveLevelContact, saddleCoordinateSwap,
      hyperbolaRadius, max_eq_right ht, min_eq_left ht, Real.sqrt_sq_eq_abs,
      abs_of_pos hr, Fin.rev]

theorem range_movingContact_eq_positive {r t : Real} (hr : 0 < r) (ht : 0 ≤ t) :
    range (movingContact r t) = range (positiveLevelContact r t) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j.2, Fin.rev j.1), (movingContact_eq_positive hr ht j).symm⟩
  · rintro ⟨⟨j, k⟩, rfl⟩
    refine ⟨(Fin.rev k, j), ?_⟩
    rw [movingContact_eq_positive hr ht]
    simp

theorem range_movingContact_eq_negative {r t : Real} (hr : 0 < r) (ht : t ≤ 0) :
    range (movingContact r t) = range (negativeLevelContact r (-t)) := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j.1, Fin.rev j.2), (movingContact_eq_negative hr ht j).symm⟩
  · rintro ⟨⟨j, k⟩, rfl⟩
    refine ⟨(j, Fin.rev k), ?_⟩
    rw [movingContact_eq_negative hr ht]
    simp

theorem movingContact_injective {r t : Real} (hr : 0 < r) (ht : |t| < r ^ 2) :
    Function.Injective (movingContact r t) := by
  intro j k hjk
  rcases le_total 0 t with ht0 | ht0
  · simp only [movingContact_eq_positive hr ht0] at hjk
    have he := positiveLevelContact_injective hr ((le_abs_self t).trans_lt ht) hjk
    exact Prod.ext (Fin.rev_injective (congrArg Prod.snd he)) (congrArg Prod.fst he)
  · simp only [movingContact_eq_negative hr ht0] at hjk
    have he := negativeLevelContact_injective hr ((neg_le_abs t).trans_lt ht) hjk
    exact Prod.ext (Prod.mk.inj he).1 (Fin.rev_injective (Prod.mk.inj he).2)

theorem square_boundary_level_eq_movingContact {r t : Real}
    (hr : 0 < r) (ht : |t| < r ^ 2) :
    (closedSquare r \ openSquare r) ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = t} =
      range (movingContact r t) := by
  rcases lt_trichotomy 0 t with ht0 | ht0 | ht0
  · rw [range_movingContact_eq_positive hr ht0.le]
    exact square_boundary_positiveLevel hr ht0 ((le_abs_self t).trans_lt ht)
  · subst t
    rw [show movingContact r 0 = contact r from funext (movingContact_zero hr)]
    simpa only [show ∀ x : E2,
      (-(x 0) ^ 2 + (x 1) ^ 2 = 0) ↔ ((x 0) ^ 2 = (x 1) ^ 2) by
        intro x; constructor <;> intro h <;> linarith] using square_boundary_zeroLevel hr
  · rw [range_movingContact_eq_negative hr ht0.le]
    simpa only [neg_neg] using
      square_boundary_negativeLevel hr (neg_pos.mpr ht0) ((neg_le_abs t).trans_lt ht)

theorem movingContact_mem_boundary {r t : Real} (hr : 0 < r) (ht : |t| < r ^ 2)
    (j : Fin 2 × Fin 2) :
    movingContact r t j ∈ closedSquare r \ openSquare r :=
  ((square_boundary_level_eq_movingContact hr ht).superset (mem_range_self j)).1

theorem movingContact_height {r t : Real} (hr : 0 < r) (ht : |t| < r ^ 2)
    (j : Fin 2 × Fin 2) :
    -(movingContact r t j 0) ^ 2 + (movingContact r t j 1) ^ 2 = t :=
  ((square_boundary_level_eq_movingContact hr ht).superset (mem_range_self j)).2

theorem image_movingContact_notMem_openSquare {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph E2 M) {r t : Real}
    (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) (ht : |t| < r ^ 2)
    (j : Fin 2 × Fin 2) : e (movingContact r t j) ∉ e '' openSquare r := by
  rintro ⟨x, hx, he⟩
  have hc := movingContact_mem_boundary hr ht j
  have hxc := e.injOn (hrs (openSquare_subset_closedSquare r hx)) (hrs hc.1) he
  exact hc.2 (hxc ▸ hx)

theorem closure_image_openSquare_subset {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph E2 M) {r : Real}
    (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    closure (e '' openSquare r) ⊆ e '' closedSquare r :=
  closure_minimal (image_mono (openSquare_subset_closedSquare r))
    ((isCompact_closedSquare hr.le).image_of_continuousOn
      (e.continuousOn.mono hrs)).isClosed

theorem frontier_image_openSquare_level_subset {M : Type*}
    [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph E2 M) {r c t : Real}
    (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    {h : M → Real}
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (ht : |t| < r ^ 2) :
    frontier (e '' openSquare r) ∩ h ⁻¹' {c + t} ⊆
      range (fun j => e (movingContact r t j)) := by
  have hopen := e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)
  rintro q ⟨hq, hqh⟩
  obtain ⟨x, hx, rfl⟩ := closure_image_openSquare_subset e hr hrs
    (frontier_subset_closure hq)
  have hxo : x ∉ openSquare r := fun hxo =>
    (hopen.frontier_eq ▸ hq).2 ⟨x, hxo, rfl⟩
  have hlevel : -(x 0) ^ 2 + (x 1) ^ 2 = t := by
    change h (e x) = c + t at hqh
    rw [hform x (hrs hx)] at hqh
    linarith
  obtain ⟨j, rfl⟩ := (square_boundary_level_eq_movingContact hr ht).subset ⟨⟨hx, hxo⟩, hlevel⟩
  exact ⟨j, rfl⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
