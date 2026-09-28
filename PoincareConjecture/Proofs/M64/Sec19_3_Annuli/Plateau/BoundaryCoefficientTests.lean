import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedTests
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChain
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryLocalization

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)





theorem m64CompactCoefficientTest_weak_derivatives
    {u : LoopPlane → E} (hu : Continuous u) {V : Fin 2 → LoopPlane → E}
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 < C)
    (hdf : ∀ z : E, ‖fderiv ℝ f z‖ ≤ C)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    ∀ i : Fin 2,
      MemLp (fun p => phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p)) 2 volume ∧
      HasWeakPartialDeriv i (fun p => phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p))
          (fun p => phi p * f (u p)) univ := by
  obtain ⟨r, hr, hsr⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : LoopPlane)
  have hquad (z : E) : ‖fderiv ℝ f z‖ ≤ C * (1 + ‖z‖ ^ 2) :=
    (hdf z).trans (by nlinarith [mul_nonneg hC.le (sq_nonneg ‖z‖)])
  have hdfu : Continuous (fun p => fderiv ℝ f (u p)) :=
    (hf.continuous_fderiv (by norm_num)).comp hu
  have hfu : Continuous (fun p => f (u p)) := hf.continuous.comp hu
  have hdu (i : Fin 2) : MemLp (fun p => fderiv ℝ f (u p) (V i p)) 2 volume := by
    apply (hV i).of_le_mul (c := C)
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hdfu.aestronglyMeasurable.prodMk (hV i).aestronglyMeasurable))
    exact Eventually.of_forall fun p =>
      ((fderiv ℝ f (u p)).le_opNorm (V i p)).trans
        (mul_le_mul_of_nonneg_right (hdf _) (norm_nonneg _))
  obtain ⟨D, hD⟩ := hp.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  intro i
  have hfirst : MemLp (fun p => phi p * fderiv ℝ f (u p) (V i p)) 2 volume := by
    apply (hdu i).of_le_mul (c := D)
      (hp.continuous.aestronglyMeasurable.mul (hdu i).aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hD ⟨p, rfl⟩) (norm_nonneg _)
  have hsecond : MemLp (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p))
      2 volume := by
    exact (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).mul hfu)
      |>.memLp_of_hasCompactSupport ((hc.fderiv_apply ℝ _).mul_right)
  refine ⟨hfirst.add hsecond, ?_⟩
  have hchain := M60.suWeakPartial_comp_quadratic hr (lt_add_one r)
    (M60.suContinuous_memLp_ball hu.continuousOn)
    (fun j => (hV j).restrict (ball 0 (r + 1)))
    (fun j k => (hw j k).restrict isOpen_ball (subset_univ _)) hf hC hquad i
  have hfuLp : MemLp (fun p => f (u p)) 2 (volume.restrict (ball 0 r ∩ univ)) := by
    simpa only [inter_univ] using M60.suContinuous_memLp_ball hfu.continuousOn
  have hduLp : MemLp (fun p => fderiv ℝ f (u p) (V i p)) 2
      (volume.restrict (ball 0 r ∩ univ)) := by
    simpa only [inter_univ] using (hdu i).restrict (ball 0 r)
  apply hasWeakPartialDeriv_mul_smooth_of_tsupport_subset isOpen_ball i hfuLp hduLp
    (by simpa only [inter_univ] using hchain) hp hc hsr





theorem m64NaturalGrowth_coefficient_mixed_test
    (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    {u : LoopPlane → E} (hu : Continuous u) {V : Fin 2 → LoopPlane → E}
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 < C)
    (hdf : ∀ z : E, ‖fderiv ℝ f z‖ ≤ C)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O)
    (hz : dirichlet → ∀ p : LoopPlane, p 1 < 0 → phi p * f (u p) = 0)
    (heq : ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * psi p) :
    (∫ p, ∑ i : Fin 2, F i p * (phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p))) =
      ∫ p, b p * (phi p * f (u p)) := by
  have htest := m64CompactCoefficientTest_weak_derivatives hu hV hw hf hC hdf hp hc
  have hcont := hp.continuous.mul (hf.continuous.comp hu)
  exact m64NaturalGrowth_mixed_boundary_test dirichlet hO hF hb hcont hc.mul_right
    (tsupport_mul_subset_left.trans hs) (hcont.memLp_of_hasCompactSupport hc.mul_right)
    (fun i => (htest i).1) (fun i => (htest i).2) hz heq

end PoincareConjecture
