import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem referenceFlattening_height_factor
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (c₂ : ℝ) (hc₂ : -1 < c₂)
    (heq : ∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z))
    (y : E3) (hy : c₂ < (heightCoordinates y).2) :
    let G0 := heightCoordinates.toDiffeomorph.trans
      (referenceFlatteningDiffeomorph a ha α hα hpos)
    let z := (heightCoordinates y).2
    let X := (G0 y).1
    let w := (referenceCapScale a) ^ 2 /
      ((1 + z) * ((referenceCapScale a) ^ 2 + ‖X‖ ^ 2))
    0 < w ∧ (G0 y).2 = w * (‖y‖ ^ 2 - 1) := by
  let G0 := heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)
  let z := (heightCoordinates y).2
  let x := (heightCoordinates y).1
  let X := (G0 y).1
  let c := referenceCapScale a
  have hc : 0 < c := referenceCapScale_pos a ha
  have hz : 0 < 1 + z := by dsimp only [z]; linarith only [hc₂, hy]
  have hd : 0 < c ^ 2 + ‖X‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖)
  have hX : X = (c / (1 + z)) • x := by
    change α z • x = (c / (1 + z)) • x
    rw [heq z hy.le]
  have hn : ‖X‖ ^ 2 * (1 + z) ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
    rw [hX, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow]
    field_simp [hz.ne']
  have hnorm : ‖y‖ ^ 2 = ‖x‖ ^ 2 + z ^ 2 := heightCoordinates_norm_sq y
  refine ⟨div_pos (sq_pos_of_pos hc) (mul_pos hz hd), ?_⟩
  change z - (c ^ 2 - ‖X‖ ^ 2) / (c ^ 2 + ‖X‖ ^ 2) =
    c ^ 2 / ((1 + z) * (c ^ 2 + ‖X‖ ^ 2)) * (‖y‖ ^ 2 - 1)
  rw [hnorm]
  field_simp [hd.ne', hz.ne']
  nlinarith only [hn]


noncomputable def referenceCapTransition
    (A : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z) :
    OpenPartialHomeomorph E3 E3 :=
  let G0 := heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)
  (G0.toHomeomorph.toOpenPartialHomeomorph.trans C).trans A.chart.symm


theorem referenceCapTransition_spec
    (A : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hC : ContDiffOn ℝ ∞ C C.source)
    (hCi : ContDiffOn ℝ ∞ C.symm C.target)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z) :
    let G0 := heightCoordinates.toDiffeomorph.trans
      (referenceFlatteningDiffeomorph a ha α hα hpos)
    let T := referenceCapTransition A C a ha α hα hpos
    T.source = {y : E3 | G0 y ∈ C.source ∧ C (G0 y) ∈ A.chart.target} ∧
    T.target = {x : E3 | x ∈ A.chart.source ∧ A.chart x ∈ C.target} ∧
    (∀ y : E3, T y = A.chart.symm (C (G0 y))) ∧
    (∀ x : E3, T.symm x = G0.symm (C.symm (A.chart x))) ∧
    ContDiffOn ℝ ∞ T T.source ∧
    ContDiffOn ℝ ∞ T.symm T.target := by
  let G0 := heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)
  let J := G0.toHomeomorph.toOpenPartialHomeomorph.trans C
  let T := referenceCapTransition A C a ha α hα hpos
  have hJ : ContDiffOn ℝ ∞ J J.source :=
    hC.comp G0.contMDiff_toFun.contDiff.contDiffOn (fun _ hy => hy.2)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target :=
    G0.contMDiff_invFun.contDiff.comp_contDiffOn (hCi.mono inter_subset_left)
  refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · ext y
    change ((y ∈ (univ : Set E3) ∧ G0 y ∈ C.source) ∧
      C (G0 y) ∈ A.chart.target) ↔
        (G0 y ∈ C.source ∧ C (G0 y) ∈ A.chart.target)
    simp only [mem_univ, true_and]
  · ext x
    change (x ∈ A.chart.source ∧ (A.chart x ∈ C.target ∧
      C.symm (A.chart x) ∈ (univ : Set (E2 × ℝ)))) ↔ _
    simp only [mem_univ, and_true, mem_ofPred_eq]
  · exact A.smooth_symm.comp (hJ.mono inter_subset_left) (fun _ hy => hy.2)
  · exact hJi.comp (A.smooth.mono inter_subset_left) (fun _ hy => hy.2)


theorem referenceCapTransition_oriented_patch
    (A : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hC : ContDiffOn ℝ ∞ C C.source)
    (hCi : ContDiffOn ℝ ∞ C.symm C.target)
    (a ε b : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hε : 0 < ε) (hb : 0 < b)
    (hzero : closedBall (0 : E2) (1 + ε) ×ˢ ({0} : Set ℝ) ⊆ C.source)
    (hcentral : ∀ X : E2, ‖X‖ ≤ 1 + ε →
      C (X, 0) = A.chart (referenceCapPoint a X))
    (hpositive : ∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
      0 < s → s < b → C (X, s) ∈ A.closedRegionᶜ)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (c₂ : ℝ) (hc₂ : c₂ ∈ Ioo (1 / 2 : ℝ) a)
    (heq : ∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z)) :
    let G0 := heightCoordinates.toDiffeomorph.trans
      (referenceFlatteningDiffeomorph a ha α hα hpos)
    let T := referenceCapTransition A C a ha α hα hpos
    let U := T.source ∩ {y : E3 |
      c₂ < (heightCoordinates y).2 ∧ ‖(G0 y).1‖ < 1 + ε ∧ |(G0 y).2| < b}
    IsOpen U ∧
    {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} ⊆ U ∧
    (∀ y ∈ U, ‖y‖ = 1 → T y = y) ∧
    (∀ y ∈ U, 1 < ‖y‖ → 1 < ‖T y‖) ∧
    ∀ y ∈ U, ‖y‖ = 1 → 0 < ⟪y, fderiv ℝ T y y⟫_ℝ := by
  let G0 := heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)
  let T := referenceCapTransition A C a ha α hα hpos
  let U := T.source ∩ {y : E3 |
    c₂ < (heightCoordinates y).2 ∧ ‖(G0 y).1‖ < 1 + ε ∧ |(G0 y).2| < b}
  obtain ⟨hTs, _, hTf, _, hT, hTi⟩ := referenceCapTransition_spec A C hC hCi a ha α hα hpos
  have hG : Continuous G0 := G0.contMDiff_toFun.continuous
  have hc₂lo : -1 < c₂ := by linarith only [hc₂.1]
  have hU : IsOpen U := T.open_source.inter
    ((isOpen_lt continuous_const heightCoordinates.continuous.snd).inter
      ((isOpen_lt hG.fst.norm continuous_const).inter
        (isOpen_lt hG.snd.abs continuous_const)))
  have hcap : {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} ⊆ U := by
    intro y hy
    have hym : y ∈ referenceCapPoint a '' closedBall (0 : E2) 1 := by
      rwa [referenceCapPoint_image_closedBall a ha]
    obtain ⟨X, hX, rfl⟩ := hym
    have hXε : ‖X‖ ≤ 1 + ε := (mem_closedBall_zero_iff.mp hX).trans (by linarith)
    have hheight : a ≤ referenceCapHeight a X := hy.2
    have hGcap : G0 (referenceCapPoint a X) = (X, 0) :=
      referenceFlattening_capPoint a ha α hα hpos c₂ heq X (hc₂.2.le.trans hheight)
    refine ⟨?_, hc₂.2.trans_le hy.2, ?_, ?_⟩
    · rw [hTs]
      change G0 (referenceCapPoint a X) ∈ C.source ∧
        C (G0 (referenceCapPoint a X)) ∈ A.chart.target
      rw [hGcap, hcentral X hXε]
      exact ⟨hzero ⟨mem_closedBall_zero_iff.mpr hXε, rfl⟩,
        A.chart.map_source (A.closedBall_subset_source
          (sphere_subset_closedBall (referenceCapPoint_mem_sphere a ha X)))⟩
    · rw [hGcap]
      exact (mem_closedBall_zero_iff.mp hX).trans_lt (by linarith)
    · rw [hGcap]
      simpa only [abs_zero] using hb
  have hfixed (y : E3) (hy : y ∈ U) (hyn : ‖y‖ = 1) : T y = y := by
    obtain ⟨_, hfactor⟩ := referenceFlattening_height_factor a ha α hα hpos c₂ hc₂lo heq y hy.2.1
    have hz : (G0 y).2 = 0 := by simpa only [hyn, one_pow, sub_self, mul_zero] using hfactor
    let X := (G0 y).1
    have hGpair : G0 y = (X, 0) := Prod.ext rfl hz
    have hheight : (heightCoordinates y).2 = referenceCapHeight a X := by
      change (heightCoordinates y).2 - referenceCapHeight a X = 0 at hz
      exact sub_eq_zero.mp hz
    have hGcap : G0 (referenceCapPoint a X) = (X, 0) :=
      referenceFlattening_capPoint a ha α hα hpos c₂ heq X
        (hheight ▸ hy.2.1.le)
    have hycap : y = referenceCapPoint a X := G0.injective (hGpair.trans hGcap.symm)
    rw [hTf, hGpair, hcentral X hy.2.2.1.le, ← hycap]
    exact A.chart.left_inv (A.closedBall_subset_source
      (mem_closedBall_zero_iff.mpr hyn.le))
  have hout (y : E3) (hy : y ∈ U) (hyn : 1 < ‖y‖) : 1 < ‖T y‖ := by
    obtain ⟨hw, hfactor⟩ := referenceFlattening_height_factor a ha α hα hpos c₂ hc₂lo heq y hy.2.1
    have hz : 0 < (G0 y).2 := by
      rw [hfactor]
      exact mul_pos hw (by nlinarith only [hyn, norm_nonneg y])
    have houtside : C (G0 y) ∈ A.closedRegionᶜ :=
      hpositive (G0 y).1 hy.2.2.1.le (G0 y).2 hz
        (lt_of_le_of_lt (le_abs_self _) hy.2.2.2)
    have hsource : C (G0 y) ∈ A.chart.target := by
      have hh := hy.1
      rw [hTs] at hh
      exact hh.2
    by_contra hnot
    have hnorm : ‖T y‖ ≤ 1 := le_of_not_gt hnot
    apply houtside
    refine ⟨T y, mem_closedBall_zero_iff.mpr hnorm, ?_⟩
    rw [hTf]
    exact A.chart.right_inv hsource
  refine ⟨hU, hcap, hfixed, hout, ?_⟩
  intro y hy hyn
  obtain ⟨L, hL⟩ := exists_smoothChart_derivative T hT hTi hy.1
  apply fderiv_normal_pos_of_local_exterior T hyn hL.differentiableAt
  · filter_upwards [hU.mem_nhds hy] with z hz
    exact hfixed z hz
  · rw [hL.fderiv]
    exact L.injective
  · filter_upwards [hU.mem_nhds hy] with z hz hzn
    rcases eq_or_lt_of_le hzn with hequal | hstrict
    · rw [hfixed z hz hequal.symm]
      exact hzn
    · exact (hout z hz hstrict).le

end PoincareConjecture.M25.Topology3D
