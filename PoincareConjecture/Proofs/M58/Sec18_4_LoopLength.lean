import PoincareConjecture.Definitions.M58LoopSmoothing
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Proofs.M58

noncomputable def angularPoint (t : ℝ) : LoopPlane := !₂[Real.cos t, Real.sin t]

theorem norm_angularPoint (t : ℝ) : ‖angularPoint t‖ = 1 := by
  simp [angularPoint, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.cos_sq_add_sin_sq]

theorem angularPoint_mem_annulus (t : ℝ) : angularPoint t ∈ loopAnnulus := by
  change 1 / 2 < ‖angularPoint t‖ ∧ ‖angularPoint t‖ < 2
  rw [norm_angularPoint]
  norm_num

theorem contDiff_angularPoint : ContDiff ℝ ∞ angularPoint := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin

noncomputable def loopCircleBasepoint : LoopCircle :=
  ⟨angularPoint 0, norm_angularPoint 0⟩

theorem exists_angularPoint (z : LoopCircle) :
    ∃ t ∈ Icc 0 rampPeriod, angularPoint t = z.val := by
  let w : ℂ := ⟨z.val 0, z.val 1⟩
  have hw : ‖w‖ = 1 := by
    have hz := EuclideanSpace.real_norm_sq_eq z.val
    rw [z.property] at hz
    have hsq : ‖w‖ ^ 2 = 1 := by
      rw [Complex.sq_norm]
      change z.val 0 * z.val 0 + z.val 1 * z.val 1 = 1
      simpa only [Fin.sum_univ_two, pow_two, one_mul] using hz.symm
    nlinarith [norm_nonneg w]
  have hcos : Real.cos w.arg = z.val 0 := by
    simpa [hw, w] using Complex.norm_mul_cos_arg w
  have hsin : Real.sin w.arg = z.val 1 := by
    simpa [hw, w] using Complex.norm_mul_sin_arg w
  by_cases harg : 0 ≤ w.arg
  · refine ⟨w.arg, ⟨harg, ?_⟩, ?_⟩
    · dsimp [rampPeriod]
      linarith [Complex.arg_le_pi w, Real.pi_pos]
    · ext i
      fin_cases i
      · exact hcos
      · exact hsin
  · refine ⟨w.arg + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg w, Real.pi_pos]
    · dsimp [rampPeriod]
      linarith
    · ext i
      fin_cases i
      · simpa [angularPoint, Real.cos_add_two_pi] using hcos
      · simpa [angularPoint, Real.sin_add_two_pi] using hsin

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem contMDiff_periodicFreeLoop (γ : C1FreeLoopSpace (M := M)) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (periodicFreeLoop γ) :=
  γ.regularity.comp_contMDiff (contDiff_angularPoint.of_le (by simp)).contMDiff
    angularPoint_mem_annulus

theorem continuous_freeLoopSpeed (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) :
    Continuous (fun t => g.tangentNorm (periodicFreeLoop γ t)
      (curveVelocity (periodicFreeLoop γ) t)) :=
  M04.continuous_pathSpeed g (contMDiff_periodicFreeLoop γ)

theorem pathELength_periodicFreeLoop (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) :
    g.pathELength (periodicFreeLoop γ) 0 rampPeriod = ENNReal.ofReal (freeLoopLength g γ) :=
  M04.pathELength_eq_ofReal_integral_pathSpeed g (contMDiff_periodicFreeLoop γ)
    (by dsimp [rampPeriod]; positivity)

theorem freeLoopLength_nonneg (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) : 0 ≤ freeLoopLength g γ :=
  intervalIntegral.integral_nonneg (by dsimp [rampPeriod]; positivity)
    (fun _ _ => Real.sqrt_nonneg _)

theorem edist_periodicFreeLoop_le_length (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) {t : ℝ} (ht : t ∈ Icc 0 rampPeriod) :
    g.edist (periodicFreeLoop γ 0) (periodicFreeLoop γ t) ≤
      ENNReal.ofReal (freeLoopLength g γ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hprefix : g.edist (periodicFreeLoop γ 0) (periodicFreeLoop γ t) ≤
      g.pathELength (periodicFreeLoop γ) 0 t :=
    Manifold.riemannianEDist_le_pathELength
      (contMDiff_periodicFreeLoop γ).contMDiffOn rfl rfl ht.1
  have hmono : g.pathELength (periodicFreeLoop γ) 0 t ≤
      g.pathELength (periodicFreeLoop γ) 0 rampPeriod :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (hprefix.trans hmono).trans_eq (pathELength_periodicFreeLoop g γ)

theorem edist_loop_le_length (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    g.edist (γ loopCircleBasepoint) (γ z) ≤ ENNReal.ofReal (freeLoopLength g γ) := by
  obtain ⟨t, ht, htz⟩ := exists_angularPoint z
  have h0 : periodicFreeLoop γ 0 = γ loopCircleBasepoint :=
    γ.boundary loopCircleBasepoint
  have hz : periodicFreeLoop γ t = γ z := by
    change γ.extension (angularPoint t) = γ z
    rw [htz]
    exact γ.boundary z
  simpa only [h0, hz] using edist_periodicFreeLoop_le_length g γ ht

theorem loop_mem_ball_of_length_lt (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) {ζ : ℝ} (hζ : 0 < ζ)
    (hshort : freeLoopLength g γ < ζ) (z : LoopCircle) :
    γ z ∈ g.ball (γ loopCircleBasepoint) ζ :=
  (edist_loop_le_length g γ z).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hζ).mpr hshort)

end PoincareConjecture.Proofs.M58
