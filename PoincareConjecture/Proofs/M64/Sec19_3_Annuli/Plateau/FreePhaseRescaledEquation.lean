import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseInteriorEquation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedInteriorSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "E" => EuclideanSpace ℝ (Fin ((n + 1) + 1))

set_option maxHeartbeats 1600000 in

theorem auxiliaryCircle_free_phase_rescaled_critical
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e Robs c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    (q : Q.charts.Point) {u : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {p0 : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : closedBall p0 R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (closedBall p0 R) (extChartAt (𝓡 ((n + 1) + 1)) q).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball p0 R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j) (ball p0 R))
    (hmap : EqOn ((extChartAt (𝓡 ((n + 1) + 1)) q).symm ∘ u)
      A.annulus.map (closedBall p0 R)) :
    let s := Real.sqrt modulus
    let D := m64SourceScale s (Real.sqrt_pos.mpr hmodulus).ne'
    ∃ radius : ℝ, M60.SUWeakAlphaCoordinate g q 1 (u ∘ D)
      (fun i p => m64SourceScaleFactor s i • W i (D p)) (D.symm p0) radius := by
  obtain ⟨rho, hrho, hrhoR, hvariation⟩ := auxiliaryCircle_free_phase_local_equation
    P Q e he hei Robs hRobs A g B hB hb hdiag modulus hminimum
      q hR hRS hu huT hW hw hmap
  let s := Real.sqrt modulus
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hmodulus).ne'
  have hs2 : s ^ 2 = modulus := Real.sq_sqrt hmodulus.le
  let D := m64SourceScale s hs
  let a' := D.symm p0
  let small := (rho / 4) * Real.exp (-1)
  have hsmall : 0 < small := mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _)
  have hsmallrho : small < rho / 2 := by
    have hh := mul_lt_of_lt_one_right (div_pos hrho (by norm_num : (0 : ℝ) < 4))
      (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
    dsimp only [small]
    linarith
  have hopen : IsOpen (D ⁻¹' ball p0 small) := isOpen_ball.preimage D.continuous
  have ha' : a' ∈ D ⁻¹' ball p0 small := by
    change D (D.symm p0) ∈ ball p0 small
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (mem_ball_self hsmall : p0 ∈ ball p0 small)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen a' ha'
  let radius := r / 2
  have hradius : 0 < radius := half_pos hr
  have hclosed : closedBall a' radius ⊆ D ⁻¹' ball p0 small :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hsource : closedBall a' radius ⊆ D ⁻¹' ball p0 R := by
    intro p hp
    exact (ball_subset_ball (show small ≤ R by linarith) :
      ball p0 small ⊆ ball p0 R) (hclosed hp)
  have hsourceHalf : ball a' radius ⊆ D ⁻¹' ball p0 (rho / 2) := by
    intro p hp
    exact (ball_subset_ball hsmallrho.le : ball p0 small ⊆ ball p0 (rho / 2))
      (hclosed (ball_subset_closedBall hp))
  let v := u ∘ D
  let V := fun i p => m64SourceScaleFactor s i • W i (D p)
  have hv : Continuous v := hu.comp D.continuous
  have hV (i : Fin 2) : MemLp (V i) 2 (volume.restrict (ball a' radius)) :=
    (((hW i).comp_measurePreserving (m64SourceScale_restrict_measurePreserving s hs
      (ball p0 R))).const_smul (m64SourceScaleFactor s i)).mono_measure
        (Measure.restrict_mono (ball_subset_closedBall.trans hsource) le_rfl)
  have hweak (i : Fin 2) (j : Fin ((n + 1) + 1)) :
      HasWeakPartialDeriv i (fun p => V i p j) (fun p => v p j) (ball a' radius) :=
    (m64SourceScale_weakPartial (hw i j) s hs).restrict isOpen_ball
      (ball_subset_closedBall.trans hsource)
  have htest (phi : LoopPlane → E) (hp : ContDiff ℝ ∞ phi)
      (hps : tsupport phi ⊆ ball a' radius) :
      IntegrableOn (M60.suAlphaChartVariation g q 1 v V phi) (ball a' radius) ∧
        (∫ p in ball a' radius, M60.suAlphaChartVariation g q 1 v V phi p) = 0 := by
    let psi := phi ∘ D.symm
    have hpsi : ContDiff ℝ ∞ psi := hp.comp D.symm.contDiff
    have hpsis : tsupport psi ⊆ ball p0 small := by
      change tsupport (phi ∘ D.toHomeomorph.symm) ⊆ ball p0 small
      rw [tsupport_comp_eq_preimage]
      intro p hp'
      have hm := hclosed (ball_subset_closedBall (hps hp'))
      change D (D.symm p) ∈ ball p0 small at hm
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hm
    let G := g.pullbackCoefficients (extChartAt (𝓡 ((n + 1) + 1)) q).symm
    let rate := fun p =>
      (modulus * (fderiv ℝ G (u p) (psi p) (W 0 p) (W 0 p) +
          2 * G (u p) (W 0 p) (fderiv ℝ psi p (EuclideanSpace.single 0 1))) +
        modulus⁻¹ * (fderiv ℝ G (u p) (psi p) (W 1 p) (W 1 p) +
          2 * G (u p) (W 1 p) (fderiv ℝ psi p (EuclideanSpace.single 1 1)))) / 2
    obtain ⟨hint, hzero⟩ := hvariation psi hpsi hpsis
    change IntegrableOn rate (ball p0 (rho / 2)) at hint
    change (∫ p in ball p0 (rho / 2), rate p) = 0 at hzero
    have heq (p : LoopPlane) : M60.suAlphaChartVariation g q 1 v V phi p =
        2 * rate (D p) := by
      have h := m64SourceScale_alphaOne_variation g q s hs u W phi hp p
      dsimp only at h
      rw [hs2] at h
      rw [h]
      dsimp only [rate, G, psi, D]
      ring
    have hint' : IntegrableOn (M60.suAlphaChartVariation g q 1 v V phi)
        (D ⁻¹' ball p0 (rho / 2)) := by
      have hmp := m64SourceScale_restrict_measurePreserving s hs (ball p0 (rho / 2))
      apply (hmp.integrable_comp_of_integrable (hint.const_mul 2)).congr
      exact Eventually.of_forall fun p => (heq p).symm
    have hzero' : (∫ p in D ⁻¹' ball p0 (rho / 2),
        M60.suAlphaChartVariation g q 1 v V phi p) = 0 := by
      simp_rw [heq]
      rw [m64SourceScale_integral s hs (ball p0 (rho / 2)) (fun p => 2 * rate p),
        integral_const_mul, hzero, mul_zero]
    refine ⟨hint'.mono_set hsourceHalf, ?_⟩
    rw [← hzero']
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_ball.preimage D.continuous).measurableSet hsourceHalf
    intro p hp'
    have hnot : p ∉ tsupport phi := fun ht => hp'.2 (hps ht)
    simp only [M60.suAlphaChartVariation, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, map_zero, zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  refine ⟨radius, hradius, ?_, hv.continuousOn, ?_, ?_, hweak, ?_, ?_⟩
  · intro p hp
    exact huT (ball_subset_closedBall (hsource hp))
  · simpa using m64MemLp_on_ball_of_continuous_closedBall hv.continuousOn 2
      (a := a') (R := radius)
  · intro i; simpa using hV i
  · intro phi hp _ hps; exact (htest phi hp hps).1
  · intro phi hp _ hps; exact (htest phi hp hps).2

end PoincareConjecture.M64
