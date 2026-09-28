import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction
import Mathlib.Geometry.Manifold.BumpFunction








set_option autoImplicit false
set_option maxSynthPendingDepth 8
open Set Filter
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric

private theorem positive_bilinear_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ B v v := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
      let := h
      refine ⟨1, by norm_num, fun v => ?_⟩
      simp [Subsingleton.elim v 0]
  | inr h =>
      let := h
      have hs : (Metric.sphere (0 : E) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (by norm_num)
      have hc : Continuous (fun v : E => B v v) := by fun_prop
      obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hc.continuousOn
      have hwn : ‖w‖ = 1 := by simpa using hw
      have hw0 : w ≠ 0 := by intro hw0; simp [hw0] at hwn
      refine ⟨B w w, hpos w hw0, fun v => ?_⟩
      by_cases hv : v = 0
      · simp [hv]
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
        simp [norm_smul, ne_of_gt hn]
      have hl : B w w ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := hmin hu
      simp only [map_smul, smul_apply, smul_eq_mul] at hl
      have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg ‖v‖)
      have heq : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * B v v)) = B v v := by
        field_simp
      rw [heq] at hm
      simpa [mul_comm] using hm


noncomputable def ofEuclideanCoefficients
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) where
  inner := B
  symm := hsymm
  pos := hpos
  isVonNBounded x := by
    obtain ⟨c, hc, hbound⟩ := positive_bilinear_lower_bound (B x) (hpos x)
    change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin n) | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin n)) (c⁻¹ + 1)).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖v‖ ^ 2 < c⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hc]
      nlinarith [hbound v]
    nlinarith [sq_nonneg (‖v‖ - 1 / 2)]
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    convert! hB.contDiffAt.contMDiffAt using 1
    ext y v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]


theorem exists_local_extension
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, g.euclideanCoefficients x = B x := by
  obtain ⟨f, _, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) p).mem_iff.mp (hU.mem_nhds hp)
  let δ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  let C : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun x => f x • B x + (1 - f x) • δ
  have hCa (x v w : EuclideanSpace ℝ (Fin n)) :
      C x v w = f x * B x v w + (1 - f x) * inner ℝ v w := rfl
  have hfs : ContDiff ℝ ∞ (fun x => f x) := contMDiff_iff_contDiff.mp f.contMDiff
  have hC : ContDiff ℝ ∞ C := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hfirst : ContDiffAt ℝ ∞ (fun y => f y • B y) x := by
      by_cases hx : x ∈ tsupport f
      · exact hfs.contDiffAt.smul ((hB x (hf hx)).contDiffAt (hU.mem_nhds (hf hx)))
      · apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
    exact hfirst.add ((contDiffAt_const.sub hfs.contDiffAt).smul contDiffAt_const)
  have hCs : ∀ x v w, C x v w = C x w v := by
    intro x v w
    rw [hCa, hCa]
    by_cases hx : f x = 0
    · simp [hx, real_inner_comm]
    · have hxU := hf (subset_tsupport f (Function.mem_support.mpr hx))
      rw [hsymm x hxU v w, real_inner_comm v w]
  have hCp : ∀ x v, v ≠ 0 → 0 < C x v v := by
    intro x v hv
    rw [hCa]
    by_cases hx : f x = 0
    · simpa [hx] using real_inner_self_pos.mpr hv
    · have hxU := hf (subset_tsupport f (Function.mem_support.mpr hx))
      have hfp : 0 < f x := lt_of_le_of_ne f.nonneg (Ne.symm hx)
      have hnonneg : 0 ≤ (1 - f x) * inner ℝ v v :=
        mul_nonneg (sub_nonneg.mpr f.le_one) real_inner_self_nonneg
      exact add_pos_of_pos_of_nonneg (mul_pos hfp (hpos x hxU v hv)) hnonneg
  let g := ofEuclideanCoefficients C hC hCs hCp
  have heq : ∀ᶠ x in 𝓝 p, g.euclideanCoefficients x = B x := by
    filter_upwards [f.eventuallyEq_one] with x hx
    change C x = B x
    ext v w
    rw [hCa, show f x = 1 from hx]
    ring
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hp) heq)
  exact ⟨g, V, hVo, hpV, fun x hx => (hV hx).1, fun x hx => (hV hx).2⟩



theorem exists_local_realization
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData g) (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, g.euclideanCoefficients x = B x := by
  obtain ⟨g, V, hV⟩ := exists_local_extension hU hp B hB hsymm hpos
  exact ⟨g, g.euclideanLeviCivitaData, V, hV⟩

end PoincareConjecture.RiemannianMetric
