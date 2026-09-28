import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem integer_translate {f : LoopPlane → ℝ}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (z : ℤ) (p : LoopPlane) : f (annulusPoint (z • curvePeriod) 0 + p) = f p := by
  have hp : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> rfl
  have hshift : annulusPoint (z • curvePeriod) 0 + p =
      annulusPoint (p 0 + z • curvePeriod) (p 1) := by
    ext i
    fin_cases i <;> simp [annulusPoint, add_comm]
  have hper : Function.Periodic (fun x => f (annulusPoint x (p 1))) curvePeriod :=
    fun x => hperiod x (p 1)
  rw [hshift]
  exact (hper.zsmul z (p 0)).trans (congrArg f hp)

private theorem translated_point {f : LoopPlane → ℝ}
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (p : LoopPlane) (hs : p 1 ∈ Icc (0 : ℝ) 1) :
    ∃ T q : LoopPlane, q ∈ m64AnnulusDomain ∧ T + p = q ∧
      ∀ r : LoopPlane, f (T + r) = f r := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let z := -toIcoDiv hP 0 (p 0)
  let T := annulusPoint (z • curvePeriod) 0
  let q := annulusPoint (toIcoMod hP 0 (p 0)) (p 1)
  have hx := toIcoMod_mem_Ico' hP (p 0)
  refine ⟨T, q, ⟨hx.1, hx.2.le, hs.1, hs.2⟩, ?_, integer_translate hperiod z⟩
  ext i
  fin_cases i <;> simp [T, q, z, annulusPoint, toIcoMod, neg_smul, sub_eq_add_neg, add_comm]

theorem m64PeriodicScalar_contDiffAt_of_fundamental
    {f : LoopPlane → ℝ} {k : ℕ∞ω}
    (hreg : ∀ p ∈ m64AnnulusDomain, ContDiffAt ℝ k f p)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {p : LoopPlane} (hp : p 1 ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ k f p := by
  obtain ⟨T, q, hq, hpoint, hfun⟩ := translated_point hperiod p hp
  have hcomp : ContDiffAt ℝ k (fun r => f (T + r)) p :=
    (hpoint.symm ▸ hreg q hq).comp p (contDiffAt_const.add contDiffAt_id)
  simpa only [show (fun r => f (T + r)) = f from funext hfun] using hcomp

private theorem laplacian_translate (f : LoopPlane → ℝ) (T p : LoopPlane) :
    Laplacian.laplacian (fun q => f (T + q)) p = Laplacian.laplacian f (T + p) := by
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ),
    laplacian_eq_iteratedFDeriv_orthonormalBasis (fun q => f (T + q))
      (EuclideanSpace.basisFun (Fin 2) ℝ), iteratedFDeriv_comp_add_left]

private theorem laplacian_continuousAt {f : LoopPlane → ℝ} {p : LoopPlane}
    (hf : ContDiffAt ℝ ∞ f p) : ContinuousAt (Laplacian.laplacian f) p := by
  have h3 : ContDiffAt ℝ 3 f p := hf.of_le (by norm_cast)
  have hd := h3.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two]
  exact (hd.continuousMultilinear_apply_const _).continuousAt.add
    (hd.continuousMultilinear_apply_const _).continuousAt

theorem m64PeriodicScalar_harmonicOnNhd_strip
    {f : LoopPlane → ℝ}
    (hreg : ∀ p ∈ m64AnnulusDomain, ContDiffAt ℝ ∞ f p)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hharm : HarmonicOnNhd f m64AnnulusInterior) :
    HarmonicOnNhd f m64AnnulusOpenStrip := by
  have hlap : EqOn (Laplacian.laplacian f) (fun _ => (0 : ℝ)) m64AnnulusDomain := by
    have hinner : EqOn (Laplacian.laplacian f) (fun _ => (0 : ℝ)) m64AnnulusInterior :=
      fun p hp => (hharm p hp).2.eq_of_nhds
    apply hinner.of_subset_closure
      (fun p hp => (laplacian_continuousAt (hreg p hp)).continuousWithinAt) continuousOn_const
    · rw [← m64AnnulusInterior_closure]
      exact subset_closure
    · rw [m64AnnulusInterior_closure]
  have hlapstrip : ∀ p ∈ m64AnnulusOpenStrip, Laplacian.laplacian f p = 0 := by
    intro p hp
    obtain ⟨T, q, hq, hpoint, hfun⟩ := translated_point hperiod p ⟨hp.1.le, hp.2.le⟩
    have heq := laplacian_translate f T p
    rw [funext hfun, hpoint] at heq
    exact heq.trans (hlap hq)
  intro p hp
  refine ⟨(m64PeriodicScalar_contDiffAt_of_fundamental hreg hperiod
    ⟨hp.1.le, hp.2.le⟩).of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞), ?_⟩
  filter_upwards [isOpen_m64AnnulusOpenStrip.mem_nhds hp] with q hq
  exact hlapstrip q hq

end PoincareConjecture
