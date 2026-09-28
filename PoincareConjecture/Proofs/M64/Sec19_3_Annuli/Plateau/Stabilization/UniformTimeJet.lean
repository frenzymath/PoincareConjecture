import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusFamily
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M64

theorem uniform_time_zero_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hf : ContDiffOn ℝ 1 f (Ioo (-epsilon) epsilon ×ˢ univ))
    {K : Set ℝ} (hK : IsCompact K)
    (hbase : ∀ x ∈ K, f (0, x) = 0)
    (hderiv : ∀ x ∈ K, fderiv ℝ f (0, x) (1, 0) = 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h ∈ Ioo (-delta) delta,
      ∀ x ∈ K, ‖f (h, x)‖ ≤ eta * |h| := by
  let U : Set (ℝ × ℝ) := Ioo (-epsilon) epsilon ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let D : ℝ × ℝ → E := fun q => fderiv ℝ f q (1, 0)
  have hD : ContinuousOn D U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hV : IsOpen (U ∩ D ⁻¹' Metric.ball (0 : E) eta) :=
    hD.isOpen_inter_preimage hU Metric.isOpen_ball
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have htube : ({0} : Set ℝ) ×ˢ K ⊆ U ∩ D ⁻¹' Metric.ball (0 : E) eta := by
    rintro ⟨h, x⟩ ⟨hh, hx⟩
    rcases mem_singleton_iff.mp hh with rfl
    refine ⟨⟨hzero, mem_univ _⟩, ?_⟩
    simpa only [mem_preimage, Metric.mem_ball, D, hderiv x hx, dist_self] using heta
  obtain ⟨J, V, hJ, -, hzeroJ, hKV, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton hK hV htube
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (hzeroJ (mem_singleton 0)))
  have hsmall : Ioo (-delta) delta ⊆ J := by
    intro h hh
    exact hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hh)
  have hpair (h : ℝ) (hh : h ∈ Ioo (-delta) delta) (x : ℝ) (hx : x ∈ K) :
      (h, x) ∈ U ∩ D ⁻¹' Metric.ball (0 : E) eta :=
    hprod ⟨hsmall hh, hKV hx⟩
  refine ⟨delta, hdelta, ?_⟩
  intro h hh x hx
  have hd (s : ℝ) (hs : s ∈ Ioo (-delta) delta) :
      HasDerivAt (fun z => f (z, x)) (D (s, x)) s := by
    have hfs := (hf.contDiffAt (hU.mem_nhds (hpair s hs x hx).1)).differentiableAt
      one_ne_zero
    exact hfs.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hb (s : ℝ) (hs : s ∈ Ioo (-delta) delta) :
      ‖deriv (fun z => f (z, x)) s‖ ≤ eta := by
    rw [(hd s hs).deriv]
    exact (show ‖D (s, x)‖ < eta by
      simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using
        (hpair s hs x hx).2).le
  have hzero' : (0 : ℝ) ∈ Ioo (-delta) delta := ⟨by linarith, hdelta⟩
  have hmean := (convex_Ioo (-delta) delta).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hb hzero' hh
  simpa only [hbase x hx, sub_zero, Real.norm_eq_abs] using hmean

end PoincareConjecture.M64
