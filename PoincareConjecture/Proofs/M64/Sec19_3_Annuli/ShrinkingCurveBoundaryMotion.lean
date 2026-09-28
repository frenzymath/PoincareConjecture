import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem m64ShrinkingCurve_exists_centered_boundary_motion
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ f : ℝ → ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
        (Ioo (-epsilon) epsilon ×ˢ univ) ∧
      (∀ r x, f r (x + curvePeriod) = f r x) ∧
      (∀ r ∈ Ioo (-epsilon) epsilon, ∀ x, f r x = c x (t + r)) ∧
      ∀ x, curveVelocity (fun r => f r x) 0 = m62CurvatureVector F c t x := by
  classical
  let epsilon := min (t - a) (b - t) / 2
  have hepsilon : 0 < epsilon :=
    half_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  have hshift (r : ℝ) (hr : r ∈ Ioo (-epsilon) epsilon) : t + r ∈ Ioo a b := by
    dsimp only [epsilon] at hr
    constructor <;>
      linarith [min_le_left (t - a) (b - t), min_le_right (t - a) (b - t),
        ht.1, ht.2, hr.1, hr.2]
  let f : ℝ → ℝ → M := fun r x => c x (if t + r ∈ Icc a b then t + r else t)
  have hagree (r : ℝ) (hr : r ∈ Ioo (-epsilon) epsilon) (x : ℝ) :
      f r x = c x (t + r) := by
    simp only [f, if_pos (Ioo_subset_Icc_self (hshift r hr))]
  have hraw : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.2 (t + q.1)) (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hc.joint_smooth.comp (contDiff_snd.prodMk
      (contDiff_const.add contDiff_fst)).contMDiff.contMDiffOn
        (fun q hq => ⟨mem_univ _, hshift q.1 hq.1⟩)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (fun q => f q.1 q.2)
      (Ioo (-epsilon) epsilon ×ˢ univ) :=
    hraw.congr (fun q hq => hagree q.1 hq.1 q.2)
  have hperiodic (r x : ℝ) : f r (x + curvePeriod) = f r x := by
    unfold f
    split_ifs with hr
    · exact hc.periodic _ hr x
    · exact hc.periodic t (Ioo_subset_Icc_self ht) x
  refine ⟨epsilon, hepsilon, f, hf, hperiodic, hagree, ?_⟩
  intro x
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have heq : (fun r => f r x) =ᶠ[𝓝 (0 : ℝ)] fun r => c x (t + r) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with r hr
    exact hagree r hr x
  have hvelocity : curveVelocity (fun r => f r x) 0 =
      curveVelocity (fun r => c x (t + r)) 0 :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
      (heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n))
  have hct : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r => c x r) t :=
    (hc.joint_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (x, t) ∈ univ ×ˢ Ioo a b from ⟨mem_univ _, ht⟩))).comp t
        (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hchain := M63.curveVelocity_comp
    (gamma := fun r => c x r) (phi := fun r => t + r)
    (by simpa only [add_zero] using hct.mdifferentiableAt (by simp))
    ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hchain' : curveVelocity (n := n) (fun r => c x (t + r)) 0 =
      curveVelocity (n := n) (fun r => c x r) (t + 0) := by
    simpa only [one_smul] using hchain
  have ht0 := congrArg (fun s : ℝ =>
    (curveVelocity (n := n) (fun r => c x r) s : EuclideanSpace ℝ (Fin n))) (add_zero t)
  exact hvelocity.trans (hchain'.trans (ht0.trans (hc.equation t ht x)))

end PoincareConjecture
