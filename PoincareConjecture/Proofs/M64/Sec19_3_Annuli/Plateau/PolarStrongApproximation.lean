import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.InnerStrongApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarPullback
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongSquareOperations

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

def m64MorreyPolarAngularColumn {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : LoopPlane) (rho : ℝ) (V : Fin 2 → LoopPlane → E) (p : LoopPlane) : E :=
  (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.single (0 : Fin 2) 1)) 0 •
      V 0 (m64MorreyPolarStrip a rho p) +
    (fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.single (0 : Fin 2) 1)) 1 •
      V 1 (m64MorreyPolarStrip a rho p)

private theorem plane_apply_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : LoopPlane →L[ℝ] E) (w : LoopPlane) :
    L w = w 0 • L (EuclideanSpace.single (0 : Fin 2) 1) +
      w 1 • L (EuclideanSpace.single (1 : Fin 2) 1) := by
  have hw : w = w 0 • EuclideanSpace.single (0 : Fin 2) 1 +
      w 1 • EuclideanSpace.single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hw, map_add, map_smul, map_smul]

theorem m64Polar_strong_transfer
    {m : ℕ} (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho)
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (huK : MemLp u 2 (volume.restrict (Metric.closedBall a rho)))
    (hVK : ∀ i, MemLp (V i) 2 (volume.restrict (Metric.closedBall a rho)))
    (f : ℕ → LoopPlane → EuclideanSpace ℝ (Fin m)) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hval : Tendsto (fun j => ∫ p in Metric.closedBall a rho, ‖f j p - u p‖ ^ 2)
      atTop (𝓝 0))
    (hcol : ∀ i, Tendsto (fun j => ∫ p in Metric.closedBall a rho,
      ‖fderiv ℝ (f j) p (EuclideanSpace.single i 1) - V i p‖ ^ 2) atTop (𝓝 0)) :
    MemLp (fun p => u (m64MorreyPolarStrip a rho p)) 2 mu ∧
      MemLp (m64MorreyPolarAngularColumn a rho V) 2 mu ∧
      Tendsto (fun j => ∫ p in S,
        ‖f j (m64MorreyPolarStrip a rho p) - u (m64MorreyPolarStrip a rho p)‖ ^ 2)
        atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ p in S,
        ‖fderiv ℝ (f j ∘ m64MorreyPolarStrip a rho) p (EuclideanSpace.single (0 : Fin 2) 1) -
          m64MorreyPolarAngularColumn a rho V p‖ ^ 2) atTop (𝓝 0) := by
  let P := m64MorreyPolarStrip a rho
  let v0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let A := fun (i : Fin 2) (p : LoopPlane) => (fderiv ℝ P p v0) i
  have hP : ContDiff ℝ ∞ P := m64MorreyPolarStrip_contDiff a rho
  have hA (i : Fin 2) : Continuous (A i) := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      ((hP.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hbd (i : Fin 2) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ m64AnnulusDomain, ‖A i p‖ ≤ C := by
    obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn
      (hA i).continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun p hp => (hC p hp).trans (le_max_right _ _)⟩
  choose C hC hbound using hbd
  have hat (i : Fin 2) : MemLp (A i) ∞ mu := by
    apply memLp_top_of_bound (hA i).aestronglyMeasurable (C i)
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hbound i p (interior_subset hp)
  have hVP (i : Fin 2) : MemLp (fun p => V i (P p)) 2 mu :=
    m64MorreyPolarStrip_memLp_two a hrho (hVK i)
  have hv : MemLp (m64MorreyPolarAngularColumn a rho V) 2 mu :=
    (MemLp.smul (hVP 0) (hat 0)).add (MemLp.smul (hVP 1) (hat 1))
  refine ⟨m64MorreyPolarStrip_memLp_two a hrho huK, hv, ?_⟩
  let D := fun j i p => fderiv ℝ (f j) p (EuclideanSpace.single i 1)
  have hD (j : ℕ) (i : Fin 2) : Continuous (D j i) :=
    ((hf j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hfl (j : ℕ) : MemLp (f j) 2 (volume.restrict (Metric.closedBall a rho)) := by
    apply (memLp_two_iff_integrable_sq_norm (hf j).continuous.aestronglyMeasurable).mpr
    exact ((hf j).continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a rho)
  have hDl (j : ℕ) (i : Fin 2) :
      MemLp (D j i) 2 (volume.restrict (Metric.closedBall a rho)) := by
    apply (memLp_two_iff_integrable_sq_norm (hD j i).aestronglyMeasurable).mpr
    exact ((hD j i).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a rho)
  let R := fun j i p => D j i (P p) - V i (P p)
  have hR (j : ℕ) (i : Fin 2) : MemLp (R j i) 2 mu :=
    (m64MorreyPolarStrip_memLp_two a hrho (hDl j i)).sub (hVP i)
  have hRlim (i : Fin 2) : Tendsto (fun j => ∫ p in S, ‖R j i p‖ ^ 2) atTop (𝓝 0) := by
    apply m64MorreyPolarStrip_strong_square_limit a hrho (fun j => D j i) (V i)
    · intro j
      exact (memLp_two_iff_integrable_sq_norm ((hDl j i).sub (hVK i)).aestronglyMeasurable).mp
        ((hDl j i).sub (hVK i))
    · exact hcol i
  have hAR (j : ℕ) (i : Fin 2) : MemLp (fun p => A i p • R j i p) 2 mu :=
    MemLp.smul (hR j i) (hat i)
  have hARlim (i : Fin 2) :
      Tendsto (fun j => ∫ p in S, ‖A i p • R j i p‖ ^ 2) atTop (𝓝 0) := by
    apply m64StrongSquare_smul (fun j => R j i) (fun j => hR j i)
      (A i) (hA i).aestronglyMeasurable (hC i) ?_ (hRlim i)
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hbound i p (interior_subset hp)
  have herr (j : ℕ) (p : LoopPlane) :
      fderiv ℝ (f j ∘ P) p v0 - m64MorreyPolarAngularColumn a rho V p =
        A 0 p • R j 0 p + A 1 p • R j 1 p := by
    rw [fderiv_comp p ((hf j).differentiable (by simp) (P p))
      (hP.differentiable (by simp) p), ContinuousLinearMap.comp_apply, plane_apply_basis]
    dsimp only [A, R, D, m64MorreyPolarAngularColumn, P, v0]
    module
  refine ⟨?_, ?_⟩
  · apply m64MorreyPolarStrip_strong_square_limit a hrho f u
    · intro j
      exact (memLp_two_iff_integrable_sq_norm ((hfl j).sub huK).aestronglyMeasurable).mp
        ((hfl j).sub huK)
    · exact hval
  · have hl := m64StrongSquare_add (fun j p => A 0 p • R j 0 p)
      (fun j p => A 1 p • R j 1 p) (fun j => hAR j 0) (fun j => hAR j 1)
      (hARlim 0) (hARlim 1)
    change Tendsto (fun j => ∫ p in S,
      ‖fderiv ℝ (f j ∘ P) p v0 - m64MorreyPolarAngularColumn a rho V p‖ ^ 2) atTop (𝓝 0)
    simp_rw [herr]
    exact hl

theorem m64WeakMap_polar_strong_approximation
    {m : ℕ} {O : Set LoopPlane} (hO : IsOpen O)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O)
    (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (hu : MemLp u 2 (volume.restrict O)) (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => u p b) O) :
    MemLp (fun p => u (m64MorreyPolarStrip a rho p)) 2 mu ∧
      MemLp (m64MorreyPolarAngularColumn a rho V) 2 mu ∧
      ∃ f : ℕ → LoopPlane → EuclideanSpace ℝ (Fin m),
        (∀ j, ContDiff ℝ ∞ (f j)) ∧
        (∀ j x s, f j (annulusPoint (x + curvePeriod) s) = f j (annulusPoint x s)) ∧
        Tendsto (fun j => ∫ p in S, ‖f j p - u (m64MorreyPolarStrip a rho p)‖ ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun j => ∫ p in S,
          ‖fderiv ℝ (f j) p (EuclideanSpace.single (0 : Fin 2) 1) -
            m64MorreyPolarAngularColumn a rho V p‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨f, hf, hval, hcol⟩ := m64WeakMap_inner_strong_approximation
    hO (isCompact_closedBall a rho) hKO u V hu hV hw
  obtain ⟨huP, hvP, hvalP, hcolP⟩ := m64Polar_strong_transfer a hrho u V
    (hu.mono_measure (Measure.restrict_mono hKO le_rfl))
    (fun i => (hV i).mono_measure (Measure.restrict_mono hKO le_rfl)) f hf hval hcol
  refine ⟨huP, hvP, fun j => f j ∘ m64MorreyPolarStrip a rho,
    fun j => (hf j).comp (m64MorreyPolarStrip_contDiff a rho), ?_, hvalP, hcolP⟩
  intro j x s
  exact congrArg (f j) (m64MorreyPolarStrip_periodic a rho x s)

end PoincareConjecture
