import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Cover.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Manifold

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Topology.OrientationDoubleCover

open PoincareConjecture.ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem decide_mul_neg (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    decide (a * b < 0) = (decide (a < 0) ^^ decide (b < 0)) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;>
    rcases lt_or_gt_of_ne hb with hb | hb
  · simp [ha, hb, not_lt_of_gt (mul_pos_of_neg_of_neg ha hb)]
  · simp [ha, not_lt_of_gt hb, mul_neg_of_neg_of_pos ha hb]
  · simp [not_lt_of_gt ha, hb, mul_neg_of_pos_of_neg ha hb]
  · simp [not_lt_of_gt ha, not_lt_of_gt hb, not_lt_of_gt (mul_pos ha hb)]

private theorem det_ne_zero_of_invertible
    {A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hA : A.IsInvertible) : A.det ≠ 0 := by
  obtain ⟨e, rfl⟩ := hA
  exact e.toLinearEquiv.isUnit_det'.ne_zero

def frameLift (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (t : ℝ) : TotalSpace M := ⟨q t, decide ((P t).det < 0)⟩

@[simp] theorem proj_frameLift (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (t : ℝ) : proj M (frameLift q P t) = q t := rfl

theorem localTriv_frameLift (q : ℝ → M)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (i : atlas (EuclideanSpace ℝ (Fin 3)) M) {t : ℝ}
    (ht : q t ∈ i.1.source) (hi : (P t).IsInvertible) :
    ((core M).localTriv i (frameLift q P t)).2 =
      decide (((mfderiv (𝓡 3) (𝓡 3) i.1 (q t)).comp (P t)).det < 0) := by
  classical
  change (decide ((P t).det < 0) ^^
    decide (transitionDet M ((core M).indexAt (q t)) i (q t) < 0)) = _
  have hd := transitionDet_ne_zero M ((core M).indexAt (q t)) i (q t)
    ⟨(core M).mem_baseSet_at _, ht⟩
  rw [transitionDet_indexAt M i (q t) ht] at hd ⊢
  have hcomp : ((mfderiv (𝓡 3) (𝓡 3) i.1 (q t)).comp (P t)).det =
      (mfderiv (𝓡 3) (𝓡 3) i.1 (q t)).det * (P t).det := LinearMap.det_comp _ _
  rw [hcomp]
  rw [decide_mul_neg _ _ hd (det_ne_zero_of_invertible hi), Bool.xor_comm]

theorem continuousOn_frameLift {q : ℝ → M} {I : Set ℝ}
    {P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hq : ContinuousOn q I)
    (hi : ∀ t ∈ I, (P t).IsInvertible)
    (hP : ∀ t ∈ I, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t) :
    ContinuousOn (frameLift q P) I := by
  intro t ht
  apply (FiberBundle.continuousWithinAt_totalSpace Bool (frameLift q P)).2
  refine ⟨hq t ht, ?_⟩
  let i := (core M).indexAt (q t)
  let Q := fun s => (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q t)) (q s)).comp (P s)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply (hP t ht)
  have hQt : Q t = P t := by
    dsimp only [Q]
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp]
  have hd : ContinuousAt (fun s => (Q s).det) t :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hQ.continuousAt
  have hdne : (Q t).det ≠ 0 := by rw [hQt]; exact det_ne_zero_of_invertible (hi t ht)
  have hc : ContinuousAt (fun s => decide ((Q s).det < 0)) t := by
    rcases lt_or_gt_of_ne hdne with hneg | hpos
    · apply (continuousAt_const (y := true)).congr_of_eventuallyEq
      filter_upwards [hd.eventually_lt_const hneg] with s hs
      simp [hs]
    · apply (continuousAt_const (y := false)).congr_of_eventuallyEq
      filter_upwards [hd.eventually_const_lt hpos] with s hs
      simp [not_lt_of_gt hs]
  apply hc.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin, (hq t ht).eventually
      ((core M).isOpen_baseSet i |>.mem_nhds ((core M).mem_baseSet_at (q t)))] with s hs hsrc
    exact localTriv_frameLift q P i hsrc (hi s hs)
  · exact localTriv_frameLift q P i ((core M).mem_baseSet_at (q t)) (hi t ht)

theorem eq_or_eq_flip_of_proj_eq {p q : TotalSpace M} (h : proj M p = proj M q) :
    p = q ∨ p = flip M q := by
  rcases p with ⟨x, b⟩
  rcases q with ⟨y, c⟩
  change x = y at h
  subst y
  cases b <;> cases c <;> simp [flip]

theorem endpoint_flip_of_lift {c d : ℝ → TotalSpace M} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn c (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hproj : ∀ t ∈ Icc a b, proj M (d t) = proj M (c t))
    (hend : c b = flip M (c a)) : d b = flip M (d a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rcases eq_or_eq_flip_of_proj_eq (hproj a ha) with hsame | hflip
  · have he := (isCoveringMap M).eqOn_of_comp_eqOn isPreconnected_Icc hd hc hproj ha hsame
    rw [he hb, he ha, hend]
  · have he := (isCoveringMap M).eqOn_of_comp_eqOn isPreconnected_Icc hd
      ((continuous_flip M).comp_continuousOn hc) hproj ha hflip
    simp only [he hb, he ha, Function.comp_apply, hend, flip_flip]

theorem det_inverse_comp_neg_of_flip_lift
    {q : ℝ → M} {c : ℝ → TotalSpace M} {a b : ℝ}
    {P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    (hab : a ≤ b) (hc : ContinuousOn c (Icc a b))
    (hproj : ∀ t ∈ Icc a b, proj M (c t) = q t)
    (hend : c b = flip M (c a))
    (hq : ContinuousOn q (Icc a b))
    (hi : ∀ t ∈ Icc a b, (P t).IsInvertible)
    (hP : ∀ t ∈ Icc a b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t) :
    ((P b).inverse.comp (P a)).det < 0 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have he := endpoint_flip_of_lift hab hc (continuousOn_frameLift hq hi hP)
    (fun t ht => (hproj t ht).symm) hend
  have hs : decide ((P b).det < 0) = !decide ((P a).det < 0) :=
    congrArg (fun p : TotalSpace M => p.2) he
  have hmul : (P b).inverse.det * (P b).det = 1 := by
    have heq : (P b).inverse.comp (P b) = ContinuousLinearMap.id ℝ _ := by
      apply ContinuousLinearMap.ext
      intro v
      exact (hi b hb).inverse_apply_self v
    have hh := congrArg ContinuousLinearMap.det heq
    change LinearMap.det ((P b).inverse.toLinearMap.comp (P b).toLinearMap) = _ at hh
    simpa only [LinearMap.det_comp, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id] using hh
  have hcomp : ((P b).inverse.comp (P a)).det = (P b).inverse.det * (P a).det :=
    LinearMap.det_comp _ _
  rw [hcomp]
  rcases lt_or_gt_of_ne (det_ne_zero_of_invertible (hi a ha)) with hna | hpa <;>
    rcases lt_or_gt_of_ne (det_ne_zero_of_invertible (hi b hb)) with hnb | hpb
  · simp [hna, hnb] at hs
  · exact mul_neg_of_pos_of_neg (by nlinarith [hmul]) hna
  · exact mul_neg_of_neg_of_pos (by nlinarith [hmul]) hpa
  · simp [not_lt_of_gt hpa, not_lt_of_gt hpb] at hs

theorem holonomy_det_neg_of_flip_endpoint :
    letI := chartedSpace M
    letI := isManifold M
    ∀ {c : ℝ → TotalSpace M} {a b : ℝ}
      {P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)},
      a ≤ b →
      (∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ c t) →
      c b = flip M (c a) →
      (∀ t ∈ Icc a b, (P t).IsInvertible) →
      (∀ t ∈ Icc a b, ∀ u,
        ContDiffAt ℝ ∞ (chartField c (c t) (fun s => P s u)) t) →
      LinearMap.det (((P b).inverse.comp
        ((mfderiv (𝓡 3) (𝓡 3) (flip M) (c a)).comp (P a))).toLinearMap) < 0 := by
  let := chartedSpace M
  let := isManifold M
  intro c a b P hab hc hend hi hP
  rw [mfderiv_flip_eq_id]
  change ((P b).inverse.comp ((ContinuousLinearMap.id ℝ _).comp (P a))).det < 0
  rw [ContinuousLinearMap.id_comp]
  apply det_inverse_comp_neg_of_flip_lift hab
    (fun t ht => (hc t ht).continuousAt.continuousWithinAt) (fun _ _ => rfl) hend
    ((isCoveringMap M).continuous.comp_continuousOn
      (fun t ht => (hc t ht).continuousAt.continuousWithinAt)) hi
  intro t ht u
  apply (hP t ht u).congr_of_eventuallyEq
  filter_upwards [(hc t ht).continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 3) (c t)).mem_nhds (mem_extChartAt_source _))]
    with s hs
  exact congrArg (fun L => L (P s u)) (mfderiv_extChartAt_proj M (c t) (c s)
    (by simpa only [mem_preimage, extChartAt_source] using hs))

end Poincare.Topology.OrientationDoubleCover
