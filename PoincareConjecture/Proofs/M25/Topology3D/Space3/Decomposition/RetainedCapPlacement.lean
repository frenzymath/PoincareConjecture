import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTransport
import Mathlib.Topology.Connected.Clopen











set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.SurgeryCapTag

variable {psi psiNew : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}



theorem cap_abs_height_bounds (C : SurgeryCapTag psi u)
    (y : E3) (hy : y ∈ C.cap) :
    3 * C.removal / 4 < |⟪(u : E3), y⟫_ℝ - C.cutHeight| ∧
      |⟪(u : E3), y⟫_ℝ - C.cutHeight| ≤ C.removal := by
  rw [C.cap_eq_image] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  let p : E2 × ℝ := ((C.profile.model q).1,
    C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2))
  have hp : p ∈ C.tube.source := C.tube_source
    ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
  have hb := surgeryCapCoordinates_south_height_bounds
    C.profile.horizontal C.profile.vertical C.profile.horizontal_smooth
    C.profile.vertical_smooth (fun z => (C.profile.horizontal_pos z).ne')
    (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos
    C.cutHeight C.sign C.removal C.scale C.profile.heightBound
    C.sign_abs C.scale_pos C.scale_small q hq (C.profile.height_bound q)
  change 3 * C.removal / 4 < C.sign * (p.2 - C.cutHeight) ∧
    C.sign * (p.2 - C.cutHeight) ≤ C.removal at hb
  have hpositive : 0 < C.sign * (p.2 - C.cutHeight) := by
    linarith [C.removal_pos, hb.1]
  have habs : |p.2 - C.cutHeight| = C.sign * (p.2 - C.cutHeight) := by
    calc
      _ = |C.sign * (p.2 - C.cutHeight)| := by rw [abs_mul, C.sign_abs, one_mul]
      _ = _ := abs_of_pos hpositive
  change 3 * C.removal / 4 < |⟪(u : E3), C.tube p⟫_ℝ - C.cutHeight| ∧
    |⟪(u : E3), C.tube p⟫_ℝ - C.cutHeight| ≤ C.removal
  rw [C.tube_height p hp, habs]
  exact hb



theorem exists_unique_retained_disc_of_height_avoidance
    (C : SurgeryCapTag psi u) (t : ℝ)
    (D : RegularSurgeryData psi u t) {delta r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta)
    (hnear : ∀ (i : Fin 2) (x : E2), |‖x‖ - 1| < delta →
      x ∈ (![D.sourceDiscs.positive, D.sourceDiscs.negative] i).source ∧
        (![D.sourceDiscs.positive, D.sourceDiscs.negative] i) x =
          D.sourceCollar (circleDirection x,
            (![1, -1] i) * (D.width / 2 * (1 - ‖x‖))))
    (havoid : ∀ y ∈ C.cap, D.width ≤ |⟪(u : E3), y⟫_ℝ - t|) :
    ∃! i : Fin 2, C.sourceCap ⊆
      (![D.sourceDiscs.positive, D.sourceDiscs.negative] i) ''
        closedBall (0 : E2) r := by
  let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
    ![D.sourceDiscs.positive, D.sourceDiscs.negative]
  let sigma : Fin 2 → ℝ := ![1, -1]
  let K : Fin 2 → Set UnitTwoSphere := fun i => e i '' closedBall 0 r
  have hsigma (i : Fin 2) : |sigma i| = 1 := by
    fin_cases i <;> norm_num [sigma]
  have hes (i : Fin 2) : closedBall 0 1 ⊆ (e i).source := by
    fin_cases i
    · exact D.sourceDiscs.positive_source
    · exact D.sourceDiscs.negative_source
  have htrim (i : Fin 2) (x : E2) (hx : x ∈ closedBall 0 1)
      (hp : e i x ∈ C.sourceCap) : x ∈ closedBall 0 r := by
    apply mem_closedBall_zero_iff.mpr
    by_contra hxnot
    have hxr : r < ‖x‖ := lt_of_not_ge hxnot
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hxpos : 0 < ‖x‖ := hr.trans hxr
    have hk : 0 < D.width / 2 := by linarith [D.width_pos]
    have ha0 : 0 ≤ D.width / 2 * (1 - ‖x‖) :=
      mul_nonneg hk.le (sub_nonneg.mpr hx1)
    have haw : D.width / 2 * (1 - ‖x‖) < D.width := by
      nlinarith [mul_pos hk hxpos, D.width_pos]
    have hband : |‖x‖ - 1| < delta := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx1)]
      linarith
    have hsabs : |sigma i * (D.width / 2 * (1 - ‖x‖))| < D.width := by
      rw [abs_mul, hsigma i, one_mul, abs_of_nonneg ha0]
      exact haw
    have hs : sigma i * (D.width / 2 * (1 - ‖x‖)) ∈
        Ioo (-D.width) D.width := abs_lt.mp hsabs
    have hformula : e i x = D.sourceCollar
        (circleDirection x, sigma i * (D.width / 2 * (1 - ‖x‖))) :=
      (hnear i x hband).2
    have hh : ⟪(u : E3), psi (e i x, 0)⟫_ℝ =
        t + sigma i * (D.width / 2 * (1 - ‖x‖)) := by
      rw [hformula, D.reconstruction _ _ hs, D.tube_height]
    have hy : psi (e i x, 0) ∈ C.cap := ⟨e i x, hp, rfl⟩
    have hge := havoid _ hy
    rw [hh, add_sub_cancel_left] at hge
    exact (not_le_of_gt hsabs) hge
  have hcover : C.sourceCap ⊆ K 0 ∪ K 1 := by
    intro p hp
    have hfull : p ∈ (D.sourceDiscs.positive '' closedBall 0 1) ∪
        (D.sourceDiscs.negative '' closedBall 0 1) := by
      rw [D.sourceDiscs.closed_cover]
      exact mem_univ p
    rcases hfull with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨x, htrim 0 x hx hp, rfl⟩
    · exact Or.inr ⟨x, htrim 1 x hx hp, rfl⟩
  have hcompact (i : Fin 2) : IsCompact (K i) := by
    apply (isCompact_closedBall (0 : E2) r).image_of_continuousOn
    apply (e i).continuousOn.mono
    intro x hx
    exact hes i (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hx).trans hr1.le))
  have hsub : closedBall (0 : E2) r ⊆ ball 0 1 := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hr1)
  have hdis : Disjoint (K 0) (K 1) :=
    D.sourceDiscs.open_disjoint.mono (image_mono hsub) (image_mono hsub)
  have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp
    C.sourceCap_isConnected.isPreconnected (K 0) (K 1)
      (hcompact 0).isClosed (hcompact 1).isClosed hcover
      (by rw [hdis.inter_eq, inter_empty])
  change ∃! i : Fin 2, C.sourceCap ⊆ K i
  rcases hparts with h0 | h1
  · refine ⟨0, h0, ?_⟩
    intro i hi
    fin_cases i
    · rfl
    · obtain ⟨q, hq⟩ := C.sourceCap_isConnected.nonempty
      exact False.elim (disjoint_left.mp hdis (h0 hq) (hi hq))
  · refine ⟨1, h1, ?_⟩
    intro i hi
    fin_cases i
    · obtain ⟨q, hq⟩ := C.sourceCap_isConnected.nonempty
      exact False.elim (disjoint_left.mp hdis (hi hq) (h1 hq))
    · rfl



theorem cap_disjoint_of_height_avoidance
    (C : SurgeryCapTag psi u) (N : SurgeryCapTag psiNew u)
    (d : ℝ) (hsmall : N.removal < d)
    (havoid : ∀ y ∈ C.cap,
      d ≤ |⟪(u : E3), y⟫_ℝ - N.cutHeight|) :
    Disjoint C.cap N.cap := by
  apply disjoint_left.mpr
  intro y hyC hyN
  exact (not_le_of_gt hsmall) ((havoid y hyC).trans (N.cap_abs_height_bounds y hyN).2)

end PoincareConjecture.M25.Topology3D.SurgeryCapTag
