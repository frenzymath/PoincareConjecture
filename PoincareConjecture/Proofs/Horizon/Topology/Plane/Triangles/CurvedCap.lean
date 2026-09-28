


import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Module
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.ParametricCoordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Local








set_option autoImplicit false
open Set Metric
open scoped ContDiff Topology Matrix

namespace Poincare.Topology.Plane.Triangles

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def capCorrection (f g : ℝ → E) (ε s : ℝ) : E :=
  dslope (dslope f 0) s ε + dslope (dslope g 0) (ε - s) ε


noncomputable def curvedCapMap (f g : ℝ → E) (ε : ℝ) (q : ℝ × ℝ) : E :=
  f q.1 + g q.2 - f 0 + (q.1 * q.2) • capCorrection f g ε q.1

theorem curvedCapMap_first_axis (f g : ℝ → E) (hbase : g 0 = f 0) (ε s : ℝ) :
    curvedCapMap f g ε (s, 0) = f s := by
  simp [curvedCapMap, hbase]

theorem curvedCapMap_second_axis (f g : ℝ → E) (ε t : ℝ) :
    curvedCapMap f g ε (0, t) = g t := by
  simp only [curvedCapMap, zero_mul, zero_smul, add_zero]
  abel

theorem curvedCapMap_hypotenuse (f g : ℝ → E) (hbase : g 0 = f 0) (ε s : ℝ) :
    curvedCapMap f g ε (s, ε - s) =
      f 0 + s • dslope f 0 ε + (ε - s) • dslope g 0 ε := by
  have hA := sub_smul_dslope (dslope f 0) s ε
  have hB : s • dslope (dslope g 0) (ε - s) ε = dslope g 0 ε - dslope g 0 (ε - s) := by
    have he : ε - (ε - s) = s := by ring
    simpa only [he] using sub_smul_dslope (dslope g 0) (ε - s) ε
  have hK : (s * (ε - s)) • capCorrection f g ε s =
      s • (dslope f 0 ε - dslope f 0 s) +
        (ε - s) • (dslope g 0 ε - dslope g 0 (ε - s)) := by
    rw [capCorrection, smul_add]
    calc
      _ = s • ((ε - s) • dslope (dslope f 0) s ε) +
          (ε - s) • (s • dslope (dslope g 0) (ε - s) ε) := by module
      _ = _ := by rw [hA, hB]
  have hf := sub_smul_dslope f 0 s
  have hg := sub_smul_dslope g 0 (ε - s)
  simp only [sub_zero] at hf hg
  rw [hbase] at hg
  simp only [curvedCapMap, hK, smul_sub, hf, hg]
  abel



theorem curvedCapMap_hypotenuse_affine (f g : ℝ → E) (hbase : g 0 = f 0)
    (ε t : ℝ) :
    curvedCapMap f g ε (t * ε, (1 - t) * ε) =
      (1 - t) • g ε + t • f ε := by
  have he : (1 - t) * ε = ε - t * ε := by ring
  rw [he, curvedCapMap_hypotenuse f g hbase]
  have hf := sub_smul_dslope f 0 ε
  have hg := sub_smul_dslope g 0 ε
  simp only [sub_zero] at hf hg
  rw [hbase] at hg
  have hrewrite :
      (t * ε) • dslope f 0 ε + (ε - t * ε) • dslope g 0 ε =
        t • (f ε - f 0) + (1 - t) • (g ε - f 0) := by
    rw [← hf, ← hg]
    module
  rw [add_assoc, hrewrite]
  module

variable [CompleteSpace E]

theorem contDiff_capCorrection {f g : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => capCorrection f g p.1 p.2) := by
  exact ((Poincare.Analysis.contDiff_dslope_uncurry
    (Poincare.Analysis.contDiff_dslope hf 0)).comp
      (contDiff_snd.prodMk contDiff_fst)).add
    ((Poincare.Analysis.contDiff_dslope_uncurry
      (Poincare.Analysis.contDiff_dslope hg 0)).comp
        ((contDiff_fst.sub contDiff_snd).prodMk contDiff_fst))

theorem contDiff_curvedCapMap {f g : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => curvedCapMap f g p.1 p.2) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.1) :=
    contDiff_fst.comp contDiff_snd
  have ht : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => p.2.2) :=
    contDiff_snd.comp contDiff_snd
  exact (((hf.comp hs).add (hg.comp ht)).sub contDiff_const).add
    ((hs.mul ht).smul ((contDiff_capCorrection hf hg).comp (contDiff_fst.prodMk hs)))



theorem hasStrictFDerivAt_curvedCapMap_zero {f g : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (L : (ℝ × ℝ) ≃L[ℝ] E)
    (hL : ∀ q : ℝ × ℝ, L q = q.1 • deriv f 0 + q.2 • deriv g 0) :
    HasStrictFDerivAt (fun p : ℝ × (ℝ × ℝ) => curvedCapMap f g p.1 p.2)
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (0, (0, 0)) := by
  let o : ℝ × (ℝ × ℝ) := (0, (0, 0))
  have hs : HasStrictFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) o :=
    hasStrictFDerivAt_fst.comp o hasStrictFDerivAt_snd
  have ht : HasStrictFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) o :=
    hasStrictFDerivAt_snd.comp o hasStrictFDerivAt_snd
  have hK := ((contDiff_capCorrection hf hg).comp
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).hasStrictFDerivAt
      (x := o) (by simp)
  convert! ((((hf.hasStrictDerivAt (x := 0) (by simp)).hasStrictFDerivAt.comp o hs).add
    ((hg.hasStrictDerivAt (x := 0) (by simp)).hasStrictFDerivAt.comp o ht)).sub
      (hasStrictFDerivAt_const (f 0) o)).add ((hs.mul ht).smul hK) using 1
  apply ContinuousLinearMap.ext
  intro q
  simpa [o] using hL q.2

private theorem exists_two_vector_equiv
    {v w : EuclideanSpace ℝ (Fin 2)}
    (hind : LinearIndependent ℝ (![v, w] : Fin 2 → EuclideanSpace ℝ (Fin 2))) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
      ∀ q : ℝ × ℝ, L q = q.1 • v + q.2 • w := by
  let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  let L := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    B.equivFun.toContinuousLinearEquiv.symm
  refine ⟨L, ?_⟩
  intro q
  change B.equivFun.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm q) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp [B, Fin.sum_univ_succ, coe_basisOfLinearIndependentOfCardEqFinrank]



theorem exists_smooth_triangular_cap_coordinates
    {f g : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbase : g 0 = f 0)
    (hind : LinearIndependent ℝ (![deriv f 0, deriv g 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)))
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hp : f 0 ∈ U) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      (∀ q, F q = curvedCapMap f g ε q) ∧
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
      F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ s : ℝ, F (s, 0) = f s) ∧
      (∀ t : ℝ, F (0, t) = g t) ∧
      (∀ t : ℝ, F (t * ε, (1 - t) * ε) = (1 - t) • g ε + t • f ε) := by
  obtain ⟨L, hL⟩ := exists_two_vector_equiv hind
  let H (p : ℝ × (ℝ × ℝ)) := curvedCapMap f g p.1 p.2
  have hH : ContDiff ℝ ∞ H := contDiff_curvedCapMap hf hg
  have hdH := hasStrictFDerivAt_curvedCapMap_zero hf hg L hL
  obtain ⟨δ, hδ, hcoords⟩ := Poincare.Analysis.exists_uniform_parametric_coordinates hH L hdH
  have hzero : H (0, (0, 0)) = f 0 := curvedCapMap_first_axis f g hbase 0 0
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp
    (hH.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (hzero ▸ hp)))
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro ε hε hεsmall
  have hεδ : ε < δ := hεsmall.trans_le (min_le_left δ η)
  have hεη : ε < η := hεsmall.trans_le (min_le_right δ η)
  obtain ⟨C, hC, hCball, hCsmooth, hCinv⟩ := hcoords ε (by simpa [abs_of_pos hε] using hεδ)
  let F := (C.symm.restrOpen U hU).symm
  have hF (q : ℝ × ℝ) : F q = H (ε, q) := hC q
  refine ⟨F, hF, ?_, fun _ hz => hz.2,
    hCsmooth.mono (fun _ hz => hz.1), hCinv.mono (fun _ hz => hz.1), ?_, ?_, ?_⟩
  · intro q hq
    have hqnorm : ‖q‖ ≤ ε := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hq.1, abs_of_nonneg hq.2.1]
      exact max_le (by linarith [hq.2.1, hq.2.2]) (by linarith [hq.1, hq.2.2])
    refine ⟨hCball ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using hqnorm.trans_lt hεδ
    · change C q ∈ U
      rw [hC]
      apply hηball
      change dist (ε, q) (0 : ℝ × (ℝ × ℝ)) < η
      rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε]
      exact max_lt hεη (hqnorm.trans_lt hεη)
  · intro s
    rw [hF]
    exact curvedCapMap_first_axis f g hbase ε s
  · intro t
    rw [hF]
    exact curvedCapMap_second_axis f g ε t
  · intro t
    rw [hF]
    exact curvedCapMap_hypotenuse_affine f g hbase ε t



theorem exists_smooth_triangular_caps
    {f g : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbase : g 0 = f 0)
    (hind : LinearIndependent ℝ (![deriv f 0, deriv g 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)))
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hp : f 0 ∈ U) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
      F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ s : ℝ, F (s, 0) = f s) ∧
      (∀ t : ℝ, F (0, t) = g t) ∧
      (∀ t : ℝ, F (t * ε, (1 - t) * ε) = (1 - t) • g ε + t • f ε) := by
  obtain ⟨δ, hδ, hF⟩ := exists_smooth_triangular_cap_coordinates hf hg hbase hind hU hp
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨F, _, hF⟩ := hF ε hε hεδ
  exact ⟨F, hF⟩



theorem exists_smooth_triangular_cap
    {f g : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hbase : g 0 = f 0)
    (hind : LinearIndependent ℝ (![deriv f 0, deriv g 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)))
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hp : f 0 ∈ U) :
    ∃ ε > 0, ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
      F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ s : ℝ, F (s, 0) = f s) ∧
      (∀ t : ℝ, F (0, t) = g t) ∧
      (∀ t : ℝ, F (t * ε, (1 - t) * ε) = (1 - t) • g ε + t • f ε) := by
  obtain ⟨δ, hδ, hc⟩ := exists_smooth_triangular_caps hf hg hbase hind hU hp
  exact ⟨δ / 2, by positivity, hc _ (by positivity) (by linarith)⟩



theorem exists_smooth_triangular_caps_of_contDiffOn
    {f g : ℝ → EuclideanSpace ℝ (Fin 2)} {A B : Set ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hf : ContDiffOn ℝ ∞ f A) (hg : ContDiffOn ℝ ∞ g B) (hbase : g 0 = f 0)
    (hind : LinearIndependent ℝ (![deriv f 0, deriv g 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)))
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hp : f 0 ∈ U) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
      F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ s ∈ Icc (0 : ℝ) ε, F (s, 0) = f s) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, F (0, t) = g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, F (t * ε, (1 - t) * ε) = (1 - t) • g ε + t • f ε) := by
  obtain ⟨f', hf', hfeq⟩ := Poincare.Analysis.exists_global_contDiff_germ hA hf hA0
  obtain ⟨g', hg', hgeq⟩ := Poincare.Analysis.exists_global_contDiff_germ hB hg hB0
  have hbase' : g' 0 = f' 0 := hgeq.eq_of_nhds.trans (hbase.trans hfeq.eq_of_nhds.symm)
  have hind' : LinearIndependent ℝ (![deriv f' 0, deriv g' 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [hfeq.deriv_eq, hgeq.deriv_eq]
    exact hind
  obtain ⟨δ, hδ, hcap⟩ := exists_smooth_triangular_caps hf' hg' hbase' hind' hU
    (hfeq.eq_of_nhds.symm ▸ hp)
  obtain ⟨r, hr, heq⟩ := Metric.mem_nhds_iff.mp (hfeq.and hgeq)
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro ε hε hεsmall
  have heqI (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ε) : f' t = f t ∧ g' t = g t := by
    apply heq
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt (hεsmall.trans_le (min_le_right δ r))
  obtain ⟨F, hsource, htarget, hsmooth, hinv, hfirst, hsecond, hthird⟩ :=
    hcap ε hε (hεsmall.trans_le (min_le_left δ r))
  refine ⟨F, hsource, htarget, hsmooth, hinv, ?_, ?_, ?_⟩
  · intro s hs
    exact (hfirst s).trans (heqI s hs).1
  · intro t ht
    exact (hsecond t).trans (heqI t ht).2
  · intro t _
    rw [hthird, (heqI ε (right_mem_Icc.mpr hε.le)).1,
      (heqI ε (right_mem_Icc.mpr hε.le)).2]

end Poincare.Topology.Plane.Triangles
