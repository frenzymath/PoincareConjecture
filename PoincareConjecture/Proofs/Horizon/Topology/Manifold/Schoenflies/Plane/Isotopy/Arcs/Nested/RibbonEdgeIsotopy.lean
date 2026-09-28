import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonCharts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Isotopy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

private theorem chart_edge_image
    (A R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (c : Real)
    (e : E1 → S1) {a b : Real} (hab : a ≤ b)
    (he : ∀ x ∈ closedBall (0 : E1) b,
      A (e x) = R (WithLp.toLp 2 ![x 0, c])) :
    (fun x => A (e x)) '' closedBall (0 : E1) a =
      (fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-a) a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hnorm : ‖x‖ ≤ a := by simpa using hx
    have hcoord := (PiLp.norm_apply_le x 0).trans hnorm
    exact ⟨x 0, abs_le.mp hcoord, (he x (closedBall_subset_closedBall hab hx)).symm⟩
  · rintro ⟨s, hs, rfl⟩
    let x : E1 := WithLp.toLp 2 ![s]
    have hx : x ∈ closedBall (0 : E1) a := by
      simpa [x, mem_closedBall, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] using
        (abs_le.mpr hs)
    exact ⟨x, hx, he x (closedBall_subset_closedBall hab hx)⟩

private theorem exists_supported_disk_isotopy_of_unit_ribbon_edge
    (A B R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (c : Real)
    {w : Real} (hw : 1 < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, c]) ∈
        (A '' sphere (0 : E2) 1) ∩ (B '' sphere (0 : E2) 1))
    (V : Set E2) (hV : IsOpen V)
    (hRV : (fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Ioo (-w) w ⊆ V)
    (hside : V ∩ (A '' closedBall 0 1) = V ∩ (B '' closedBall 0 1))
    (O : Set E2) (hO : IsOpen O)
    (hAO : (A '' closedBall (0 : E2) 1) \
      ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-1) 1) ⊆ O)
    (hBO : (B '' closedBall (0 : E2) 1) \
      ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-1) 1) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-1) 1) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        Phi 1 '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  obtain ⟨r, hr, hrw⟩ := exists_between hw
  obtain ⟨e, he, hes, hei, heR⟩ := exists_chart_of_ribbon_edge A R c
    (zero_lt_one.trans hr) hrw (fun s hs => (hedge s hs).1)
  obtain ⟨f, hf, hfs, hfi, hfR⟩ := exists_chart_of_ribbon_edge B R c
    (zero_lt_one.trans hr) hrw (fun s hs => (hedge s hs).2)
  let E : PartialDiffeomorph (𝓡 1) (𝓡 1) E1 S1 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hes
    contMDiffOn_invFun := hei }
  let F : PartialDiffeomorph (𝓡 1) (𝓡 1) E1 S1 ∞ := {
    toPartialEquiv := f.toPartialEquiv
    open_source := f.open_source
    open_target := f.open_target
    contMDiffOn_toFun := hfs
    contMDiffOn_invFun := hfi }
  have heimage := chart_edge_image A R c e hr.le heR
  rw [← heimage] at hAO hBO ⊢
  apply BoundaryGerm.exists_supported_disk_isotopy_of_common_arc A B hr e f
    (e.injOn.mono he) (fun x hx => ⟨E, he hx, fun _ _ => rfl⟩)
    (f.injOn.mono hf) (fun x hx => ⟨F, hf hx, fun _ _ => rfl⟩)
    (fun x hx => (heR x hx).trans (hfR x hx).symm) V hV _ hside O hO hAO hBO
  rw [chart_edge_image A R c e le_rfl heR]
  exact (image_mono (Icc_subset_Ioo (by linarith) hrw)).trans hRV

private def horizontalScale (a : Real) (ha : a ≠ 0) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![a * x 0, x 1]
  invFun x := WithLp.toLp 2 ![x 0 / a, x 1]
  left_inv x := by ext i; fin_cases i <;> simp [ha]
  right_inv x := by
    ext i
    fin_cases i
    · change a * (x 0 / a) = x 0
      field_simp
    · rfl
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.div_const a
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

theorem exists_supported_disk_isotopy_of_shared_ribbon_edge
    (A B R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (c : Real)
    {a w : Real} (ha : 0 < a) (haw : a < w)
    (hedge : ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, c]) ∈
        (A '' sphere (0 : E2) 1) ∩ (B '' sphere (0 : E2) 1))
    (V : Set E2) (hV : IsOpen V)
    (hRV : (fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Ioo (-w) w ⊆ V)
    (hside : V ∩ (A '' closedBall 0 1) = V ∩ (B '' closedBall 0 1))
    (O : Set E2) (hO : IsOpen O)
    (hAO : (A '' closedBall (0 : E2) 1) \
      ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-a) a) ⊆ O)
    (hBO : (B '' closedBall (0 : E2) 1) \
      ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-a) a) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-a) a) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        Phi 1 '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  let T := (horizontalScale a ha.ne').trans R
  have hT (s : Real) : T (WithLp.toLp 2 ![s, c]) =
      R (WithLp.toLp 2 ![a * s, c]) := rfl
  have hinterval (s : Real) (hs : s ∈ Ioo (-(w / a)) (w / a)) :
      a * s ∈ Ioo (-w) w := by
    constructor
    · have h := (div_lt_iff₀ ha).mp (show -w / a < s by simpa only [neg_div] using hs.1)
      nlinarith
    · have h := (lt_div_iff₀ ha).mp hs.2
      nlinarith
  have himage : (fun s : Real => T (WithLp.toLp 2 ![s, c])) '' Icc (-1) 1 =
      (fun s : Real => R (WithLp.toLp 2 ![s, c])) '' Icc (-a) a := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨a * s, ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, (hT s).symm⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s / a, ⟨?_, ?_⟩, ?_⟩
      · apply (le_div_iff₀ ha).mpr
        linarith [hs.1]
      · apply (div_le_iff₀ ha).mpr
        linarith [hs.2]
      · change T (WithLp.toLp 2 ![s / a, c]) = R (WithLp.toLp 2 ![s, c])
        rw [hT]
        congr 2
        field_simp
  rw [← himage] at hAO hBO ⊢
  apply exists_supported_disk_isotopy_of_unit_ribbon_edge A B T c
    ((one_lt_div ha).mpr haw) _ V hV _ hside O hO hAO hBO
  · intro s hs
    rw [hT]
    exact hedge _ (hinterval s hs)
  · rintro y ⟨s, hs, rfl⟩
    change T (WithLp.toLp 2 ![s, c]) ∈ V
    rw [hT]
    exact hRV (mem_image_of_mem _ (hinterval s hs))

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
