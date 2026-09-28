import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCircleTraces












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58




theorem m64LowerExtension_circle_fixed_trace
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : LoopPlane → M} {c gamma : ℝ → M}
    (hc : Continuous c) (hgamma : Continuous gamma)
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ} (hr : 0 < r)
    (htrace : gamma =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)]
      (fun x => m64AnnulusLowerExtend (fun p => c (p 0)) f
        (a + r • angularPoint (x - Real.pi)))) :
    EqOn gamma (fun x => c ((a + r • angularPoint (x - Real.pi)) 0))
      (Icc (0 : ℝ) Real.pi) := by
  have hsub : Ioo (0 : ℝ) Real.pi ⊆ Icc (0 : ℝ) curvePeriod := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le.trans (by unfold curvePeriod; linarith [Real.pi_pos])⟩
  have hfixed (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) Real.pi) :
      m64AnnulusLowerExtend (fun p => c (p 0)) f
        (a + r • angularPoint (x - Real.pi)) =
        c ((a + r • angularPoint (x - Real.pi)) 0) := by
    have hy : (a + r • angularPoint (x - Real.pi)) 1 < 0 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, angularPoint,
        Matrix.cons_val_one, Matrix.cons_val_zero, ha, zero_add, Real.sin_sub_pi]
      exact mul_neg_of_pos_of_neg hr (neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2))
    simp only [m64AnnulusLowerExtend, if_pos hy]
    congr 1
    simp [m64AnnulusRadialTranslation, annulusPoint]
  have htarget : Continuous (fun x => c ((a + r • angularPoint (x - Real.pi)) 0)) := by
    have hang : Continuous (fun x : ℝ => angularPoint (x - Real.pi)) :=
      contDiff_angularPoint.continuous.comp
        (show Continuous (fun x : ℝ => x - Real.pi) from continuous_id.sub continuous_const)
    have hp : Continuous (fun x : ℝ => a + r • angularPoint (x - Real.pi)) :=
      continuous_const.add (hang.const_smul r)
    exact hc.comp ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp hp)
  have hae : gamma =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
      (fun x => c ((a + r • angularPoint (x - Real.pi)) 0)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub htrace,
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact hx.trans (hfixed x hxI)
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
    hgamma.continuousOn htarget.continuousOn
  exact heq.of_subset_closure hgamma.continuousOn htarget.continuousOn Ioo_subset_Icc_self
    (by rw [closure_Ioo Real.pi_ne_zero.symm])

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 gamma : ℝ → M}



theorem M64ObservedWeakAnnulus.lower_circle_fixed_trace
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hei : IsClosedEmbedding e) (hc0 : Continuous c0) (hgamma : Continuous gamma)
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ} (hr : 0 < r)
    (htrace : gamma =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)]
      (fun x => A.lowerExtensionMap (a + r • angularPoint (x - Real.pi)))) :
    EqOn gamma (fun x => c0 ((a + r • angularPoint (x - Real.pi)) 0))
      (Icc (0 : ℝ) Real.pi) := by
  let : T2Space M := hei.isEmbedding.t2Space
  exact m64LowerExtension_circle_fixed_trace hc0 hgamma ha hr htrace



theorem M64ObservedWeakAnnulus.lower_circle_endpoints
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hei : IsClosedEmbedding e) (hc0 : Continuous c0) (hgamma : Continuous gamma)
    {a : LoopPlane} (ha : a 1 = 0) {r : ℝ} (hr : 0 < r)
    (htrace : gamma =ᵐ[volume.restrict (Icc (0 : ℝ) curvePeriod)]
      (fun x => A.lowerExtensionMap (a + r • angularPoint (x - Real.pi)))) :
    gamma 0 = c0 (a 0 - r) ∧ gamma Real.pi = c0 (a 0 + r) := by
  have ht := A.lower_circle_fixed_trace hei hc0 hgamma ha hr htrace
  constructor
  · simpa [angularPoint, sub_eq_add_neg] using ht ⟨le_rfl, Real.pi_pos.le⟩
  · simpa [angularPoint] using ht ⟨Real.pi_pos.le, le_rfl⟩

end PoincareConjecture
