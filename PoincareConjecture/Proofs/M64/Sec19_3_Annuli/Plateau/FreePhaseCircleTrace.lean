import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusCircleTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMapCircleGreen









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem m64WeakScalar_local_circle_trace
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho)
    (hKO : closedBall a rho ⊆ O) (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ)
    (hu : MemLp u 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u O) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ L : ℝ → ℝ, Continuous L ∧ Function.Periodic L curvePeriod ∧
        (L =ᵐ[circleMu] fun x => u (m64MorreyPolarStrip a rho (annulusPoint x s))) ∧
        ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
          (∫ p in closedBall a (rho * Real.exp (-s)), phi p * V i p) +
            (∫ p in closedBall a (rho * Real.exp (-s)),
              fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
            rho * Real.exp (-s) * ∫ x in Icc (0 : ℝ) curvePeriod,
              angularPoint (x - Real.pi) i *
                (phi (a + (rho * Real.exp (-s)) • angularPoint (x - Real.pi)) * L x) := by
  let U : LoopPlane → EuclideanSpace ℝ (Fin 1) :=
    fun p => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => u p)
  let W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin 1) :=
    fun i p => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => V i p)
  have hU : MemLp U 2 (volume.restrict O) := MemLp.of_eval_piLp (fun _ => hu)
  have hW (i : Fin 2) : MemLp (W i) 2 (volume.restrict O) :=
    MemLp.of_eval_piLp (fun _ => hV i)
  have hweak (i : Fin 2) (j : Fin 1) :
      HasWeakPartialDeriv i (fun p => W i p j) (fun p => U p j) O := hw i
  obtain ⟨hUp, hWp, f, hf, hperiod, hval, hder⟩ :=
    m64WeakMap_polar_strong_approximation hO a hrho hKO U W hU hW hweak
  have hslices := m64Annulus_h1_slices_of_strong_approximation f
    (fun j => (hf j).of_le (by simp)) hperiod
    (U ∘ m64MorreyPolarStrip a rho) (m64MorreyPolarAngularColumn a rho W)
    hUp hWp hval hder
  have hgreens := m64WeakMap_local_circle_green hO a hrho hKO U W hU hW hweak
  filter_upwards [hslices, hgreens, ae_restrict_mem measurableSet_Icc] with s hs hgreen hsI
  obtain ⟨-, -, Z, -, hZ, hends, hZU, -, -, -⟩ := hs
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hZ0 : ContinuousOn (fun x => Z x 0) (Icc (0 : ℝ) curvePeriod) :=
    (EuclideanSpace.proj 0).continuous.comp_continuousOn hZ
  obtain ⟨L, hL, hLP, hLZ⟩ := m64Curve_periodic_extension
    (fun x => Z x 0) hP hZ0 (congrArg (fun z => z 0) hends)
  have hLA : L =ᵐ[circleMu] fun x => u (m64MorreyPolarStrip a rho (annulusPoint x s)) := by
    filter_upwards [hZU, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact (hLZ hxI).trans (congrArg (fun z => z 0) hx)
  refine ⟨L, hL, hLP, hLA, ?_⟩
  intro phi hphi i
  let r := rho * Real.exp (-s)
  let T : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hK : closedBall a r ⊆ O := by
    exact (closedBall_subset_closedBall (show r ≤ rho from by
      dsimp only [r]
      apply mul_le_of_le_one_right hrho.le
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr hsI.1)).trans hKO
  have htest {f : LoopPlane → ℝ} (hf : Continuous f) :
      MemLp f 2 (volume.restrict (closedBall a r)) := by
    apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    exact (hf.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall a r)
  have hp := htest hphi.continuous
  have hd := htest ((hphi.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := EuclideanSpace.single i 1)))
  have hIV := m64L2_test_integrable
    ((hW i).mono_measure (Measure.restrict_mono hK le_rfl)) hp
  have hIU := m64L2_test_integrable
    (hU.mono_measure (Measure.restrict_mono hK le_rfl)) hd
  let lift : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun x => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => L x)
  have hlift : Continuous lift :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => hL)
  have hangular : Continuous (fun x : ℝ => angularPoint (x - Real.pi)) := by
    unfold angularPoint
    fun_prop
  have hcircle : Continuous (fun x : ℝ => a + r • angularPoint (x - Real.pi)) :=
    continuous_const.add (hangular.const_smul r)
  have hIR : IntegrableOn (fun x : ℝ => angularPoint (x - Real.pi) i •
      (phi (a + r • angularPoint (x - Real.pi)) • lift x))
      (Icc (0 : ℝ) curvePeriod) :=
    (((EuclideanSpace.proj i).continuous.comp hangular).smul
      ((hphi.continuous.comp hcircle).smul hlift)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hrhs : (∫ x in Icc (0 : ℝ) curvePeriod,
      angularPoint (x - Real.pi) i •
        (phi (a + r • angularPoint (x - Real.pi)) •
          U (a + r • angularPoint (x - Real.pi)))) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        angularPoint (x - Real.pi) i •
          (phi (a + r • angularPoint (x - Real.pi)) • lift x) := by
    apply integral_congr_ae
    filter_upwards [hLA] with x hx
    have heq : U (a + r • angularPoint (x - Real.pi)) = lift x := by
      ext j
      exact hx.symm
    rw [heq]
  have hrepr := hgreen phi hphi i
  change (∫ p in closedBall a r, phi p • W i p) +
    (∫ p in closedBall a r, fderiv ℝ phi p (EuclideanSpace.single i 1) • U p) =
      r • ∫ x in Icc (0 : ℝ) curvePeriod, angularPoint (x - Real.pi) i •
        (phi (a + r • angularPoint (x - Real.pi)) •
          U (a + r • angularPoint (x - Real.pi))) at hrepr
  rw [hrhs] at hrepr
  have hproj := congrArg T hrepr
  simp only [map_add, map_smul] at hproj
  rw [← T.integral_comp_comm hIV, ← T.integral_comp_comm hIU,
    ← T.integral_comp_comm hIR] at hproj
  simpa +instances only [T, Function.comp_apply, map_smul, EuclideanSpace.coe_proj,
    U, W, lift, smul_eq_mul] using! hproj

end PoincareConjecture
