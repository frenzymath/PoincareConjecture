import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapUnionSeparators
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphObstacleWidth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_trimmed_arc_avoids_caps
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ} (hr : 0 < r) (hrT : r < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    {C : Set AnnulusCoordinates}
    (hcontact : C ∩ gamma '' Icc 0 T ⊆ gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T) :
    ∀ t ∈ Ioo r (T - r), gamma t ∉ C := by
  intro t ht hmem
  have htI : t ∈ Ico (0 : ℝ) T :=
    ⟨(hr.trans ht.1).le, ht.2.trans (sub_lt_self T hr)⟩
  have h := hcontact ⟨hmem, t, ⟨htI.1, htI.2.le⟩, rfl⟩
  rcases h with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
  · have hst := hinj ⟨hs.1, hs.2.trans_lt hrT⟩ htI heq
    linarith [hs.2, ht.1]
  · by_cases hsT : s = T
    · rw [hsT, ← hend] at heq
      have hst := hinj ⟨le_rfl, hr.trans hrT⟩ htI heq
      linarith [ht.1]
    · have hsI : s ∈ Ico (0 : ℝ) T :=
        ⟨(sub_pos.mpr hrT).le.trans hs.1, lt_of_le_of_ne hs.2 hsT⟩
      have hst := hinj hsI htI heq
      linarith [hs.1, ht.2]

private theorem rotated_inner (u v : AnnulusCoordinates) :
    inner ℝ (-quarterTurn v) u = inner ℝ (quarterTurn u) v := by
  have h := inner_quarterTurn_self (u + v)
  simp only [map_add, inner_add_left, inner_add_right, inner_quarterTurn_self] at h
  calc
    inner ℝ (-quarterTurn v) u = -inner ℝ u (quarterTurn v) := by
      rw [inner_neg_left, real_inner_comm]
    _ = inner ℝ v (quarterTurn u) := by linarith
    _ = inner ℝ (quarterTurn u) v := real_inner_comm _ _

theorem m64Intrinsic_exists_internal_obstacle_barrier
    {C : Set AnnulusCoordinates} (hC : IsClosed C)
    {p v d : AnnulusCoordinates} (hp : p ∉ C)
    (hd : 0 < inner ℝ (quarterTurn v) d) (terminal : Bool) :
    ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ p ∈ W ∧ ell d = 0 ∧
      (if terminal then ell v < 0 else 0 < ell v) ∧
      ∀ z ∈ C ∩ W, ell (z - p) ≤ 0 := by
  let N := innerSL ℝ (-quarterTurn d)
  have hNd : N d = 0 := by
    change inner ℝ (-quarterTurn d) d = 0
    rw [inner_neg_left, real_inner_comm, inner_quarterTurn_self, neg_zero]
  have hNv : 0 < N v := by
    change 0 < inner ℝ (-quarterTurn d) v
    rwa [rotated_inner]
  refine ⟨if terminal then -N else N, Cᶜ, hC.isOpen_compl, hp, ?_, ?_, ?_⟩
  · cases terminal <;> simp [hNd]
  · cases terminal
    · exact hNv
    · exact neg_neg_of_pos hNv
  · intro z hz
    exact (hz.2 hz.1).elim

end PoincareConjecture
