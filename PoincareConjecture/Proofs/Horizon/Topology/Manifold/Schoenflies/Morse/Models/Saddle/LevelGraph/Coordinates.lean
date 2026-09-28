import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.LocalLevel



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)


def closedSquare (r : Real) : Set E2 := {x | |x 0| ≤ r ∧ |x 1| ≤ r}


def openSquare (r : Real) : Set E2 := {x | |x 0| < r ∧ |x 1| < r}


def contact (r : Real) (i : Fin 2 × Fin 2) : E2 :=
  WithLp.toLp 2 ![if i.1 = 0 then r else -r, if i.2 = 0 then r else -r]

theorem isClosed_closedSquare (r : Real) : IsClosed (closedSquare r) :=
  (isClosed_le ((EuclideanSpace.proj 0).continuous.abs) continuous_const).inter
    (isClosed_le ((EuclideanSpace.proj 1).continuous.abs) continuous_const)

theorem isOpen_openSquare (r : Real) : IsOpen (openSquare r) :=
  (isOpen_lt ((EuclideanSpace.proj 0).continuous.abs) continuous_const).inter
    (isOpen_lt ((EuclideanSpace.proj 1).continuous.abs) continuous_const)

theorem openSquare_subset_closedSquare (r : Real) : openSquare r ⊆ closedSquare r :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

theorem zero_mem_openSquare {r : Real} (hr : 0 < r) : (0 : E2) ∈ openSquare r := by
  simpa [openSquare] using And.intro hr hr

theorem closedSquare_subset_closedBall {r : Real} (hr : 0 ≤ r) :
    closedSquare r ⊆ closedBall 0 (2 * r) := by
  intro x hx
  have h0 := (sq_le_sq₀ (abs_nonneg (x 0)) hr).mpr hx.1
  have h1 := (sq_le_sq₀ (abs_nonneg (x 1)) hr).mpr hx.2
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  rw [sq_abs] at h0 h1
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg x]

theorem isCompact_closedSquare {r : Real} (hr : 0 ≤ r) : IsCompact (closedSquare r) :=
  (isCompact_closedBall (0 : E2) (2 * r)).of_isClosed_subset
    (isClosed_closedSquare r) (closedSquare_subset_closedBall hr)

theorem contact_mem {r : Real} (hr : 0 < r) (i : Fin 2 × Fin 2) :
    contact r i ∈ closedSquare r \ openSquare r ∧
      (contact r i) 0 ^ 2 = (contact r i) 1 ^ 2 := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [contact, closedSquare, openSquare, abs_of_pos hr]

theorem contact_injective {r : Real} (hr : 0 < r) : Function.Injective (contact r) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have h0 := congrArg (fun x : E2 => x 0) h
  have h1 := congrArg (fun x : E2 => x 1) h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [contact] at h0 h1 ⊢ <;> linarith


theorem square_boundary_zeroLevel {r : Real} (hr : 0 < r) :
    (closedSquare r \ openSquare r) ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2} =
      range (contact r) := by
  ext x
  constructor
  · rintro ⟨⟨hx, hxo⟩, heq⟩
    have habs : |x 0| = |x 1| :=
      (sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
        (by simpa only [sq_abs, mem_ofPred_eq] using heq)
    have h0 : |x 0| = r := by
      by_contra hne
      have hlt := lt_of_le_of_ne hx.1 hne
      exact hxo ⟨hlt, habs ▸ hlt⟩
    have h1 : |x 1| = r := habs ▸ h0
    rcases (abs_eq hr.le).mp h0 with h0 | h0 <;>
      rcases (abs_eq hr.le).mp h1 with h1 | h1
    · refine ⟨(0, 0), ?_⟩
      ext i
      fin_cases i <;> simp [contact, h0, h1]
    · refine ⟨(0, 1), ?_⟩
      ext i
      fin_cases i <;> simp [contact, h0, h1]
    · refine ⟨(1, 0), ?_⟩
      ext i
      fin_cases i <;> simp [contact, h0, h1]
    · refine ⟨(1, 1), ?_⟩
      ext i
      fin_cases i <;> simp [contact, h0, h1]
  · rintro ⟨i, rfl⟩
    exact contact_mem hr i


theorem exists_closedSquare_subset_source {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph E2 M) (he0 : 0 ∈ e.source) :
    ∃ r : Real, 0 < r ∧ closedSquare r ⊆ e.source := by
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  refine ⟨R / 4, by positivity, ?_⟩
  intro x hx
  apply hRs
  have hn := closedSquare_subset_closedBall (show 0 ≤ R / 4 by positivity) hx
  rw [mem_closedBall_zero_iff] at hn
  rw [mem_ball_zero_iff]
  linarith


theorem square_zeroLevel_subset_component {M : Type*} [TopologicalSpace M]
    {h : M → Real} (e : OpenPartialHomeomorph E2 M) {r c : Real}
    (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2) :
    e '' (closedSquare r ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2}) ⊆
      connectedComponentIn (h ⁻¹' {c}) (e 0) := by
  let K := closedSquare r ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2}
  have hzero : (0 : E2) ∈ K := by simp [K, closedSquare, hr.le]
  have hstar : StarConvex Real (0 : E2) K := by
    intro x hx a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    simp only [smul_zero, zero_add]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change |b * x 0| ≤ r
      rw [abs_mul, abs_of_nonneg hb]
      exact (mul_le_mul_of_nonneg_left hx.1.1 hb).trans (by nlinarith)
    · change |b * x 1| ≤ r
      rw [abs_mul, abs_of_nonneg hb]
      exact (mul_le_mul_of_nonneg_left hx.1.2 hb).trans (by nlinarith)
    · change (b * x 0) ^ 2 = (b * x 1) ^ 2
      rw [mul_pow, mul_pow, hx.2]
  have hconn : IsPreconnected (e '' K) :=
    (hstar.isPathConnected hzero).isConnected.isPreconnected.image e
      (e.continuousOn.mono (inter_subset_left.trans hrs))
  apply hconn.subset_connectedComponentIn (mem_image_of_mem e hzero)
  rintro q ⟨x, hx, rfl⟩
  change h (e x) = c
  rw [hform x (hrs hx.1), hx.2]
  ring

end Poincare.Manifold.Schoenflies.SaddleLevel
