import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RibbonSides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.RibbonMarking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.PairRegion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private def flipRibbon : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![x 0, 1 - x 1]
  invFun x := WithLp.toLp 2 ![x 0, 1 - x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact contDiff_const.sub (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact contDiff_const.sub (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

theorem exists_disk_pair_isotopy_fixing_prescribed_compact_shared_ribbon
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (hB : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1))
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w a : Real} (hw : 0 < w) (ha : 0 < a) (haw : a < w)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (havoid : ∀ s ∈ Ioo (-w) w,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        ((frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1)) ∪
          (frontier (B 0 '' closedBall 0 1) ∪ frontier (B 1 '' closedBall 0 1)))) :
    ∃ K : Set E2, IsCompact K ∧ Disjoint K
      ((fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1)) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧
          ((fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
            (Icc (-a) a ×ˢ Icc 0 1)) ⊆ U ∧ ∀ t, EqOn (Φ t) id U := by
  classical
  let T (i : Fin 2) := if i = 0 then R else flipRibbon.trans R
  have hTeq (i : Fin 2) (s : Real) :
      T i (WithLp.toLp 2 ![s, 0]) = R (WithLp.toLp 2 ![s, (i : Real)]) := by
    fin_cases i
    · simp [T]
    · change R (WithLp.toLp 2 ![s, 1 - 0]) = _
      simp
  have hmarksA (i : Fin 2) := exists_boundary_marking_of_prescribed_ribbon_edge
    (A i) (T i) hw ha haw (fun s hs => by rw [hTeq]; exact (hedge i s hs).1)
  have hmarksB (i : Fin 2) := exists_boundary_marking_of_prescribed_ribbon_edge
    (B i) (T i) hw ha haw (fun s hs => by rw [hTeq]; exact (hedge i s hs).2)
  choose rA hrA harA f hfi hfl hf using hmarksA
  choose rB hrB harB g hgi hgl hg using hmarksB
  let r := min (min (rA 0) (rA 1)) (min (rB 0) (rB 1))
  have hr : 1 < r := lt_min (lt_min (hrA 0) (hrA 1)) (lt_min (hrB 0) (hrB 1))
  have hrAle (i : Fin 2) : r ≤ rA i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
  have hrBle (i : Fin 2) : r ≤ rB i := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hfedge (i : Fin 2) (x : E1) (hx : x ∈ closedBall 0 r) :
      A i (f i x) = R (WithLp.toLp 2 ![a * x 0, (i : Real)]) :=
    (hf i x (closedBall_subset_closedBall (hrAle i) hx)).trans (hTeq i _)
  have hgedge (i : Fin 2) (x : E1) (hx : x ∈ closedBall 0 r) :
      B i (g i x) = R (WithLp.toLp 2 ![a * x 0, (i : Real)]) :=
    (hg i x (closedBall_subset_closedBall (hrBle i) hx)).trans (hTeq i _)
  have hside (i : Fin 2) : ∃ V : Set E2, IsOpen V ∧
      (fun s : Real => R (WithLp.toLp 2 ![s, (i : Real)])) '' Ioo (-w) w ⊆ V ∧
      V ∩ (A i '' closedBall 0 1) = V ∩ (B i '' closedBall 0 1) := by
    fin_cases i
    · simpa using exists_filled_coincidence_of_shared_unnested_ribbon A B hA hB R hw
        (fun s hs => by simpa using hedge 0 s hs)
        (fun s hs => by
          simpa using (show R (WithLp.toLp 2 ![s, ((1 : Fin 2) : Real)]) ∈
            (A 1 '' closedBall 0 1) ∩ (B 1 '' closedBall 0 1) from
            ⟨image_mono sphere_subset_closedBall (hedge 1 s hs).1,
              image_mono sphere_subset_closedBall (hedge 1 s hs).2⟩)) havoid
    · have hreversed : ∀ s ∈ Ioo (-w) w,
          Disjoint ((fun t : Real => (flipRibbon.trans R) (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
            ((frontier (A 1 '' closedBall 0 1) ∪ frontier (A 0 '' closedBall 0 1)) ∪
              (frontier (B 1 '' closedBall 0 1) ∪ frontier (B 0 '' closedBall 0 1))) := by
        intro s hs
        apply disjoint_left.mpr
        rintro x ⟨t, ht, rfl⟩ hx
        apply disjoint_left.mp (havoid s hs)
          (mem_image_of_mem _ (show 1 - t ∈ Ioo (0 : Real) 1 from
            ⟨by linarith [ht.2], by linarith [ht.1]⟩))
        change R (WithLp.toLp 2 ![s, 1 - t]) ∈ _ at hx
        simpa only [union_comm] using hx
      obtain ⟨V, hV, hedgeV, heq⟩ :=
        exists_filled_coincidence_of_shared_unnested_ribbon ![A 1, A 0] ![B 1, B 0]
          hA.symm hB.symm (flipRibbon.trans R) hw
          (fun s hs => by
            change R (WithLp.toLp 2 ![s, 1 - 0]) ∈ _
            simpa using hedge 1 s hs)
          (fun s hs => by
            change R (WithLp.toLp 2 ![s, 1 - 1]) ∈ _
            simpa using (show R (WithLp.toLp 2 ![s, ((0 : Fin 2) : Real)]) ∈
              (A 0 '' closedBall 0 1) ∩ (B 0 '' closedBall 0 1) from
              ⟨image_mono sphere_subset_closedBall (hedge 0 s hs).1,
                image_mono sphere_subset_closedBall (hedge 0 s hs).2⟩)) hreversed
      refine ⟨V, hV, ?_, heq⟩
      rintro _ ⟨s, hs, rfl⟩
      have h := hedgeV (mem_image_of_mem _ hs)
      change R (WithLp.toLp 2 ![s, 1 - 0]) ∈ V at h
      simpa using h
  choose V hV hedgeV hfilled using hside
  have hparam (x : E1) (hx : x ∈ closedBall 0 r) : a * x 0 ∈ Ioo (-w) w := by
    have hnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hcoord : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    apply abs_lt.mp
    rw [abs_mul, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left (hcoord.trans (hnorm.trans (hrAle 0))) ha.le).trans_lt
      (harA 0)
  have hcover (i : Fin 2) :
      (fun s : Real => R (WithLp.toLp 2 ![s, (i : Real)])) '' Icc (-a) a ⊆
        (fun x => A i (f i x)) '' closedBall (0 : E1) 1 := by
    rintro _ ⟨s, hs, rfl⟩
    let x : E1 := WithLp.toLp 2 ![s / a]
    have hx : x ∈ closedBall (0 : E1) 1 := by
      rw [mem_closedBall, dist_zero_right]
      have hxnorm : ‖x‖ = |s / a| := by
        simp [x, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs, abs_div]
      rw [hxnorm, abs_div, abs_of_pos ha]
      exact (div_le_one ha).mpr (abs_le.mpr hs)
    refine ⟨x, hx, ?_⟩
    change A i (f i x) = R (WithLp.toLp 2 ![s, (i : Real)])
    rw [hfedge i x (closedBall_subset_closedBall hr.le hx)]
    have hax : a * x 0 = s := by
      change a * (s / a) = s
      field_simp
    rw [hax]
  have hin {s : Real} (hs : s ∈ Icc (-a) a) : s ∈ Ioo (-w) w := by
    constructor <;> linarith [hs.1, hs.2]
  let P := (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
    (Icc (-a) a ×ˢ Icc 0 1)
  have hAP := compact_ribbon_meets_disjoint_disks_only_on_edges A hA R R.continuous a
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall (hedge 0 s (hin hs)).1)
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall (hedge 1 s (hin hs)).1)
    (fun s hs => (havoid s (hin hs)).mono_right subset_union_left)
  have hBP := compact_ribbon_meets_disjoint_disks_only_on_edges B hB R R.continuous a
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall (hedge 0 s (hin hs)).2)
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall (hedge 1 s (hin hs)).2)
    (fun s hs => (havoid s (hin hs)).mono_right subset_union_right)
  obtain ⟨K, hK, hKP, _, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦmatch, U, hU, hPU, hΦU⟩ :=
    exists_supported_disjoint_disk_pair_isotopy_away_closed_region A B hA hB hr f g
      (fun i => (hfi i).mono (closedBall_subset_closedBall (hrAle i)))
      (fun i x hx => hfl i x (closedBall_subset_closedBall (hrAle i) hx))
      (fun i => (hgi i).mono (closedBall_subset_closedBall (hrBle i)))
      (fun i x hx => hgl i x (closedBall_subset_closedBall (hrBle i) hx))
      (fun i x hx => (hfedge i x hx).trans (hgedge i x hx).symm)
      V hV (fun i => by
        rintro _ ⟨x, hx, rfl⟩
        change A i (f i x) ∈ V i
        rw [hfedge i x hx]
        exact hedgeV i (mem_image_of_mem _ (hparam x hx))) hfilled
      P hAP.1.isClosed
      (fun i => (hAP.2 i).trans (hcover i)) (fun i => (hBP.2 i).trans (hcover i))
  exact ⟨K, hK, hKP, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦmatch, U, hU, hPU, hΦU⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
