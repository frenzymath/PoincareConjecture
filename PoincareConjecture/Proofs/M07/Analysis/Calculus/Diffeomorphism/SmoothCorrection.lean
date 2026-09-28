import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology Manifold

namespace Poincare.Analysis.Calculus

theorem exists_smooth_relative_correction_sequence
    {d : ℕ} {V K : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hlocal : ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen W ∧ x ∈ W ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hjet : ∀ m C, IsCompact C → C ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m id) atTop C) :
    ∃ W S : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧ IsCompact S ∧ S ⊆ V ∧
      ∃ a : ℕ → EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d),
        (∀ᶠ k in atTop, ContDiff ℝ ∞ (a k) ∧ ContDiff ℝ ∞ (a k).symm ∧
          EqOn (a k) (f k) W ∧ (∀ x, x ∉ S → a k x = x) ∧
          (∀ x, f k x = x → a k x = x) ∧
          ∀ U : Set (EuclideanSpace ℝ (Fin d)), S ⊆ U → (a k) '' U = U) ∧
        ∀ m C, IsCompact C → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop C := by
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  obtain ⟨C, hC, hCc, hK'C, hCV⟩ := exists_compact_closed_between hK' hV hK'V
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, EuclideanSpace ℝ (Fin d))) hK'.isClosed hK'C (n := ⊤)
  have hχ : ContDiff ℝ ∞ (χ : EuclideanSpace ℝ (Fin d) → ℝ) := χ.contMDiff.contDiff
  have hsupport : tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ C := by
    apply closure_minimal _ hCc
    intro x hx
    by_contra hxc
    exact hx (hχzero x hxc)
  have hχc : HasCompactSupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) :=
    hC.of_isClosed_subset isClosed_closure hsupport
  have hχV := hsupport.trans hCV
  have hzero (B : Set (EuclideanSpace ℝ (Fin d))) (hB : IsCompact B) (hBV : B ⊆ V) :
      TendstoUniformlyOn f id atTop B := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin d))).comp_tendstoUniformlyOn (hjet 0 B hB hBV)
  have hone : TendstoUniformlyOn (fun k => fderiv ℝ (f k))
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))
      atTop (tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ)) := by
    have hid (q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
        (fun x => continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin d))
          (EuclideanSpace ℝ (Fin d)) (iteratedFDeriv ℝ 1 q x)) = fderiv ℝ q := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    have hid' : fderiv ℝ (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) =
        fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
      funext x
      exact fderiv_id
    simpa only [Function.comp_def, hid, hid'] using
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin d))
        (EuclideanSpace ℝ (Fin d))).isometry.uniformContinuous.comp_tendstoUniformlyOn
        (hjet 1 _ hχc.isCompact hχV)
  have hcor := eventually_exists_cutoff_diffeomorphism_of_contDiffAt hχ hχc
    (eventually_contDiffAt_on_compact_of_locally_eventually_smooth hχc.isCompact hχV hlocal)
    (hzero _ hχc.isCompact hχV) hone
  obtain ⟨a, ha⟩ := hcor.choice
  refine ⟨interior K', tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ),
    isOpen_interior, hKK', interior_subset.trans hK'V, hχc.isCompact, hχV, a, ?_, ?_⟩
  · filter_upwards [ha] with k hk
    refine ⟨hk.2.1, hk.2.2.1, ?_, hk.2.2.2.2, ?_, ?_⟩
    · intro x hx
      exact hk.2.2.2.1 x (hχone.self_of_nhdsSet x (interior_subset hx))
    · intro x hx
      simp only [hk.1 x, hx, sub_self, smul_zero, add_zero]
    · intro U hSU
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_contra hy
        have hxy := (a k).injective (hk.2.2.2.2 (a k x) (fun h => hy (hSU h)))
        exact hy (hxy.symm ▸ hx)
      · intro hy
        refine ⟨(a k).symm y, ?_, (a k).apply_symm_apply y⟩
        by_contra hx
        have hey := hk.2.2.2.2 ((a k).symm y) (fun h => hx (hSU h))
        rw [(a k).apply_symm_apply] at hey
        exact hx (hey ▸ hy)
  · intro m B hB
    have hpoint : ∀ x ∈ V, Tendsto (fun k => f k x) atTop (𝓝 x) := by
      intro x hx
      exact (hzero {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
        (mem_singleton x)
    have hconv := tendstoUniformlyOn_cutoff_perturbation_jet hpoint hlocal
      (locallyEventuallyBoundedDerivatives_of_tendsto_jets hV contDiff_id.contDiffOn hjet)
      hχ hχc hχV m hB
    apply hconv.congr
    filter_upwards [ha] with k hk x _
    exact congrArg (fun q => iteratedFDeriv ℝ m q x) (funext hk.1).symm

end Poincare.Analysis.Calculus
