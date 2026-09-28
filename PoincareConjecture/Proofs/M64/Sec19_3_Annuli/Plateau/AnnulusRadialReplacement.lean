import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialWeakExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityChartEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusReplacement













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "L" => m64AnnulusLowerStrip



theorem m64AnnulusLower_integral_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ O)
    (f : LoopPlane → E) (hf : IntegrableOn f K volume) :
    (∫ p in K, f p) = (∫ p in K ∩ S, f p) + ∫ p in K ∩ L, f p := by
  have heq : K =ᵐ[volume] ((K ∩ S) ∪ (K ∩ L) : Set LoopPlane) := by
    filter_upwards [m64AnnulusLowerDomain_ae_union] with p hp
    apply propext
    constructor
    · intro hpK
      rcases hp.mp (hKO hpK) with hpS | hpL
      · exact Or.inl ⟨hpK, hpS⟩
      · exact Or.inr ⟨hpK, hpL⟩
    · rintro (hp | hp) <;> exact hp.1
  have hdis : Disjoint (K ∩ S) (K ∩ L) :=
    m64AnnulusLower_disjoint.mono inter_subset_right inter_subset_right
  rw [setIntegral_congr_set heq]
  exact setIntegral_union hdis (hK.inter m64AnnulusLowerStrip_isOpen.measurableSet)
    (hf.mono_set inter_subset_left) (hf.mono_set inter_subset_left)

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "mu" => volume.restrict S



theorem M64ObservedWeakAnnulus.lower_fixed_columns
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (a : LoopPlane) (r : ℝ) (hKO : ball a r ⊆ O)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a r)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) (ball a r))
    (hfixed : ∀ p ∈ ball a r, p 1 < 0 → f p = c0 (p 0)) :
    f =ᵐ[volume.restrict (ball a r ∩ L)] A.lowerExtensionMap ∧
      ∀ i, V i =ᵐ[volume.restrict (ball a r ∩ L)] A.lowerExtensionColumn i := by
  let D := ball a r ∩ L
  have hD : IsOpen D := isOpen_ball.inter m64AnnulusLowerStrip_isOpen
  have hDK : D ⊆ ball a r := inter_subset_left
  have hDO : D ⊆ O := hDK.trans hKO
  have hvalue : f =ᵐ[volume.restrict D] A.lowerExtensionMap := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    have hlow := ((m64AnnulusLowerStrip_coordinates p).mp hp.2).2.2.2
    have hmap : A.lowerExtensionMap p = c0 (p 0) := by
      rw [M64ObservedWeakAnnulus.lowerExtensionMap,
        m64AnnulusLowerExtend_left _ _ hp.2]
      simp only [m64AnnulusRadialTranslation, annulusPoint, PiLp.add_apply,
        Matrix.cons_val_zero, zero_add]
    exact (hfixed p hp.1 hlow).trans hmap.symm
  refine ⟨hvalue, ?_⟩
  exact m64WeakColumns_ae_eq hD
    (fun i => (hV i).mono_measure (Measure.restrict_mono hDK le_rfl))
    (fun i => ((A.lower_extension_memLp hc0).2 i).mono_measure
      (Measure.restrict_mono hDO le_rfl))
    (fun i b => (hw i b).restrict hD hDK)
    (fun i b => (A.lower_extension_weak_partial hc0 i b).restrict hD hDO)
    (hvalue.mono fun p hp => congrArg e hp)

set_option maxHeartbeats 1000000 in



theorem M64ObservedWeakAnnulus.lower_replace
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (a : LoopPlane) (r : ℝ) (hKO : ball a r ⊆ O)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict (ball a r)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a r)))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict (ball a r),
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) (ball a r))
    (hfixed : ∀ p ∈ ball a r, p 1 < 0 → f p = c0 (p 0))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in ball a r, phi p • V i p) +
        (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in ball a r, phi p • A.lowerExtensionColumn i p) +
        (∫ p in ball a r,
          fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.lowerExtensionMap p))) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      B.map = (ball a r ∩ S).piecewise f A.map ∧
      ∀ i, (B.column i : LoopPlane → E) =ᵐ[mu]
        (ball a r ∩ S).piecewise (V i) (A.column i) := by
  classical
  let K := ball a r
  let D := K ∩ L
  obtain ⟨hmaplower, hcolumn⟩ := A.lower_fixed_columns hc0 a r hKO f V hV hw hfixed
  have hvalue : (e ∘ f) =ᵐ[volume.restrict D] (e ∘ A.lowerExtensionMap) :=
    hmaplower.mono fun p hp => congrArg e hp
  have hold := A.lower_extension_memLp hc0
  apply A.replace (measurableSet_ball.inter isOpen_interior.measurableSet) inter_subset_right
    f V (hf.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    (fun i => ae_restrict_of_ae_restrict_of_subset inter_subset_left (ht i))
  intro phi hphi i
  let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hdc : Continuous dphi := (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have htest {g : LoopPlane → ℝ} (hg : Continuous g) : MemLp g 2 (volume.restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    exact (hg.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  have hp := htest hphi.continuous
  have hd := htest hdc
  have hcolold := (hold.2 i).mono_measure (Measure.restrict_mono hKO le_rfl)
  have hobsold := hold.1.mono_measure (Measure.restrict_mono hKO le_rfl)
  have hfull := hgreen phi hphi i
  change (∫ p in K, phi p • V i p) + (∫ p in K, dphi p • e (f p)) =
    (∫ p in K, phi p • A.lowerExtensionColumn i p) +
      (∫ p in K, dphi p • e (A.lowerExtensionMap p)) at hfull
  rw [m64AnnulusLower_integral_local measurableSet_ball hKO
      (fun p => phi p • V i p) (m64L2_test_integrable (hV i) hp),
    m64AnnulusLower_integral_local measurableSet_ball hKO
      (fun p => dphi p • e (f p)) (m64L2_test_integrable hf hd),
    m64AnnulusLower_integral_local measurableSet_ball hKO
      (fun p => phi p • A.lowerExtensionColumn i p) (m64L2_test_integrable hcolold hp),
    m64AnnulusLower_integral_local measurableSet_ball hKO
      (fun p => dphi p • e (A.lowerExtensionMap p)) (m64L2_test_integrable hobsold hd)] at hfull
  have hvlo : (∫ p in D, phi p • V i p) = ∫ p in D, phi p • A.lowerExtensionColumn i p :=
    integral_congr_ae ((hcolumn i).mono fun p hp => congrArg (fun x : E => phi p • x) hp)
  have hulo : (∫ p in D, dphi p • e (f p)) =
      ∫ p in D, dphi p • e (A.lowerExtensionMap p) :=
    integral_congr_ae (hvalue.mono fun p hp => congrArg (fun x : E => dphi p • x) hp)
  have hvup : (∫ p in K ∩ S, phi p • A.lowerExtensionColumn i p) =
      ∫ p in K ∩ S, phi p • A.column i p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_ball.inter isOpen_interior.measurableSet)] with p hp
    rw [M64ObservedWeakAnnulus.lowerExtensionColumn, m64AnnulusLowerExtend_right _ _ hp.2]
  have huup : (∫ p in K ∩ S, dphi p • e (A.lowerExtensionMap p)) =
      ∫ p in K ∩ S, dphi p • e (A.map p) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_ball.inter isOpen_interior.measurableSet)] with p hp
    rw [M64ObservedWeakAnnulus.lowerExtensionMap, m64AnnulusLowerExtend_right _ _ hp.2]
  change (∫ p in K ∩ S, phi p • V i p) + (∫ p in K ∩ S, dphi p • e (f p)) = _
  rw [hvup, huup, hvlo, hulo] at hfull
  exact add_right_cancel (show
    ((∫ p in K ∩ S, phi p • V i p) + (∫ p in K ∩ S, dphi p • e (f p))) +
      ((∫ p in D, phi p • A.lowerExtensionColumn i p) +
        (∫ p in D, dphi p • e (A.lowerExtensionMap p))) =
    ((∫ p in K ∩ S, phi p • A.column i p) + (∫ p in K ∩ S, dphi p • e (A.map p))) +
      ((∫ p in D, phi p • A.lowerExtensionColumn i p) +
        (∫ p in D, dphi p • e (A.lowerExtensionMap p))) from by
    simpa only [add_assoc, add_left_comm, add_comm] using hfull)

end PoincareConjecture
