import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryErrorLocalization
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusLowerContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

omit [IsManifold (𝓡 n) ∞ M] in

theorem lower_representative_eq_boundary_below
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : Continuous c0) {F : LoopPlane → M} (hF : ContinuousOn F O)
    (hFae : F =ᵐ[volume.restrict O] A.lowerExtensionMap)
    (htrace : ∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 0) = c0 x) :
    ∀ p ∈ O, p 1 ≤ 0 → F p = c0 (p 0) := by
  have hboundary : Continuous (fun p : LoopPlane => c0 (p 0)) :=
    hc0.comp (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
  have heq : EqOn F (fun p : LoopPlane => c0 (p 0)) m64AnnulusLowerStrip := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ m64AnnulusLowerStrip_isOpen
      (hF.mono m64AnnulusLower_strip_subset) hboundary.continuousOn
    filter_upwards [ae_restrict_of_ae_restrict_of_subset m64AnnulusLower_strip_subset hFae,
      ae_restrict_mem m64AnnulusLowerStrip_isOpen.measurableSet] with p hp hpL
    rw [hp, lowerExtensionMap, m64AnnulusLowerExtend_left _ _ hpL]
    simp only [m64AnnulusRadialTranslation, annulusPoint, PiLp.add_apply,
      Matrix.cons_val_zero, zero_add]
  intro p hp hp1
  rcases lt_or_eq_of_le hp1 with hneg | hzero
  · exact heq ((m64AnnulusLowerStrip_coordinates p).mpr
      ⟨hp.1, hp.2.1, hp.2.2.1, hneg⟩)
  · have hpoint : p = annulusPoint (p 0) 0 := by
      ext i
      fin_cases i <;> simp [annulusPoint, hzero]
    simpa only [← hpoint] using htrace (p 0) ⟨hp.1, hp.2.1⟩

omit [IsManifold (𝓡 n) ∞ M] [T2Space M] in

theorem lower_boundary_error_weak_data
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : Continuous e) (hc0 : ContDiff ℝ 1 (e ∘ c0))
    {F : LoopPlane → M} (hF : ContinuousOn F O)
    (hFae : F =ᵐ[volume.restrict O] A.lowerExtensionMap)
    {a : LoopPlane} {R : ℝ} (hRO : closedBall a R ⊆ O) :
    let C : LoopPlane → E := fun p => e (c0 (p 0))
    let u : LoopPlane → E := fun p => e (F p) - C p
    let V : Fin 2 → LoopPlane → E := fun i p =>
      A.lowerExtensionColumn i p - fderiv ℝ C p (EuclideanSpace.single i 1)
    ContinuousOn u (closedBall a R) ∧ MemLp u 2 (volume.restrict (ball a R)) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict (ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (ball a R) := by
  let C : LoopPlane → E := fun p => e (c0 (p 0))
  let D : Fin 2 → LoopPlane → E := fun i p =>
    fderiv ℝ C p (EuclideanSpace.single i 1)
  have hC : ContDiff ℝ 1 C := by
    simpa only [C, Function.comp_def] using m64BoundaryCurvePlane_contDiff hc0
  have hBO : ball a R ⊆ O := ball_subset_closedBall.trans hRO
  have hobs : (fun p => e (A.lowerExtensionMap p)) =ᵐ[volume.restrict (ball a R)]
      (fun p => e (F p)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBO hFae] with p hp
    exact congrArg e hp.symm
  have hobsM : MemLp (fun p => e (F p)) 2 (volume.restrict (ball a R)) :=
    (((A.lower_extension_memLp hc0).1).mono_measure
      (Measure.restrict_mono hBO le_rfl)).ae_eq hobs
  have hCM := m64MemLp_on_ball_of_continuous_closedBall hC.continuous.continuousOn 2
    (a := a) (R := R)
  have hDM (i : Fin 2) : MemLp (D i) 2 (volume.restrict (ball a R)) :=
    m64MemLp_on_ball_of_continuous_closedBall
      ((hC.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn 2
  have hAM (i : Fin 2) : MemLp (A.lowerExtensionColumn i) 2
      (volume.restrict (ball a R)) :=
    ((A.lower_extension_memLp hc0).2 i).mono_measure (Measure.restrict_mono hBO le_rfl)
  refine ⟨(he.comp_continuousOn (hF.mono hRO)).sub hC.continuous.continuousOn,
    hobsM.sub hCM, fun i => (hAM i).sub (hDM i), ?_⟩
  intro i j
  let P := EuclideanSpace.proj (𝕜 := ℝ) j
  have hwA : HasWeakPartialDeriv i (fun p => A.lowerExtensionColumn i p j)
      (fun p => e (F p) j) (ball a R) := by
    apply m64WeakPartialDeriv_ae_congr (hobs.fun_comp P)
      (Eventually.of_forall fun _ => rfl)
    exact (A.lower_extension_weak_partial hc0 i j).restrict isOpen_ball hBO
  have hwC : HasWeakPartialDeriv i (fun p => D i p j) (fun p => C p j) (ball a R) := by
    have h := HasWeakPartialDeriv.of_contDiff (Ω := ball a R) isOpen_ball
      (P.contDiff.comp hC) (i := i)
    have hder (p : LoopPlane) : fderiv ℝ (P ∘ C) p = P.comp (fderiv ℝ C p) := by
      rw [fderiv_comp _ P.differentiableAt (hC.differentiable (by simp) _), P.fderiv]
    simp only [hder, ContinuousLinearMap.comp_apply] at h
    exact h
  have h := m64WeakPartial_add (P.comp_memLp' hobsM)
    ((P.comp_memLp' hCM).const_mul (-1)) (P.comp_memLp' (hAM i))
    ((P.comp_memLp' (hDM i)).const_mul (-1)) hwA (m64WeakPartial_const_mul hwC (-1))
  simpa only [neg_one_mul, ← sub_eq_add_neg, PiLp.sub_apply, P,
    EuclideanSpace.coe_proj, Function.comp_apply, D, C] using h

theorem weighted_exists_lower_zero_boundary_tests [CompactSpace M]
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ F : LoopPlane → M, ContinuousOn F O ∧
      F =ᵐ[volume.restrict O] A.lowerExtensionMap ∧
      (∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 0) = c0 x) ∧
      ∀ x ∈ Ioo (0 : ℝ) curvePeriod,
        ∃ R : ℝ, 0 < R ∧ closedBall (annulusPoint x 0) R ⊆ O ∧
          ∃ chi : LoopPlane → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
            tsupport chi ⊆ ball (annulusPoint x 0) R ∧
            (∀ p ∈ ball (annulusPoint x 0) (R / 2),
              chi p = 1 ∧ fderiv ℝ chi p = 0) ∧
            ∀ j : Fin m, MemW01p 2
              (fun p => chi p * (e (F p) j - e (c0 (p 0)) j))
              {p : LoopPlane | 0 < p 1} := by
  obtain ⟨F, hF, hFae, htrace⟩ := A.weighted_lower_continuous_representative
    g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmodulus hmin
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  refine ⟨F, hF, hFae, htrace, ?_⟩
  intro x hx
  have ha : annulusPoint x 0 ∈ O :=
    ⟨hx.1, hx.2, by norm_num [annulusPoint], by norm_num [annulusPoint]⟩
  obtain ⟨R, hR, hRO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (m64AnnulusLowerDomain_isOpen.mem_nhds ha)
  let u : LoopPlane → E := fun p => e (F p) - e (c0 (p 0))
  let V : Fin 2 → LoopPlane → E := fun i p => A.lowerExtensionColumn i p -
    fderiv ℝ (fun q : LoopPlane => e (c0 (q 0))) p (EuclideanSpace.single i 1)
  obtain ⟨hu, hup, hV, hw⟩ := A.lower_boundary_error_weak_data he.continuous hce hF hFae hRO
  have hz : ∀ p ∈ closedBall (annulusPoint x 0) R, p 1 ≤ 0 → u p = 0 := by
    intro p hp hp1
    dsimp only [u]
    rw [A.lower_representative_eq_boundary_below hc0.continuous hF hFae htrace p
      (hRO hp) hp1, sub_self]
  obtain ⟨chi, hchi, hc, hs, hone, htests⟩ := m64WeakBoundaryError_localization
    (u := u) (V := V) hR (by rfl) hu hup hV hw hz
  exact ⟨R, hR, hRO, chi, hchi, hc, hs, hone, fun j => (htests j).1⟩

end PoincareConjecture.M64ObservedWeakAnnulus
