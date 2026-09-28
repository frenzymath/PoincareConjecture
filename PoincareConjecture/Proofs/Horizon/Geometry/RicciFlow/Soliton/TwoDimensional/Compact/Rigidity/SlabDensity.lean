import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Coarea
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.RegularLevels
import PoincareConjecture.Proofs.Horizon.Topology.Maps.ProperRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem exists_constant_slab_density_of_surface_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hRnonneg : ∀ x, 0 ≤ D.scalarCurvature x)
    {p z : M} (hp : D.gradient f p = 0) (hpz : f p < f z) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s t : ℝ, f p < s → t < f z → s ≤ t →
      ∀ H : ℝ → ℝ, Continuous H →
        (∫ x in f ⁻¹' Icc s t, H (f x) ∂g.volumeMeasure) =
          c * ∫ u in Icc s t, H u := by
  have hfs := D.contMDiff_of_C2_surface_soliton hf hsol
  let q : ℝ → ℝ := fun t =>
    2 * lambda * (t - f p) - D.scalarCurvature p * (Real.exp (t - f p) - 1)
  let r : ℝ → ℝ := fun t => D.scalarCurvature p * Real.exp (t - f p)
  have hQ (x : M) : D.levelQ f x = q (f x) :=
    D.gradient_normSq_eq_at_critical_point hf hsol hp x
  have hR (x : M) : D.scalarCurvature x = r (f x) :=
    D.scalar_eq_exp_potential_difference_of_surface_soliton hf hsol p x
  have hreg (x : M) (hx : f x ∈ Ioo (f p) (f z)) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro hh
    exact D.gradient_ne_zero_at_intermediate_value hlambda hf hsol hx.1 hx.2 (hRnonneg x)
      ((g.gradient_eq_zero_iff_mfderiv_eq_zero f x).mpr hh)
  have hq (t : ℝ) (ht : t ∈ Ioo (f p) (f z)) : 0 < q t := by
    obtain ⟨x, hx⟩ := intermediate_value_univ p z hf.continuous (Ioo_subset_Icc_self ht)
    rw [← hx, ← hQ]
    exact Real.sqrt_pos.mp ((g.tangentNorm_gradient_pos_iff f x).mpr
      (hreg x (by rwa [hx])))
  have hqd (t : ℝ) : HasDerivAt q (2 * lambda - r t) t := by
    have hu := (hasDerivAt_id t).sub_const (f p)
    convert (hu.const_mul (2 * lambda)).sub ((hu.exp.sub_const 1).const_mul
      (D.scalarCurvature p)) using 1 <;> first | rfl | simp [r]
  have hproper : IsProperMap ((Ioo (f p) (f z)).restrictPreimage f) :=
    Poincare.isProperMap_real_restrictPreimage_of_isCompact hf.continuous _
      isCompact_univ (subset_univ _)
  obtain ⟨c, hc⟩ := D.exists_const_regularLevelArea_div_sqrt_of_surface_soliton hfs hsol
    hproper hreg (fun x _ => hQ x) (fun x _ => hR x) hq (fun t _ => hqd t)
  have hm : (f p + f z) / 2 ∈ Ioo (f p) (f z) := by constructor <;> linarith
  refine ⟨c, ?_, ?_⟩
  · rw [← hc _ hm]
    exact div_nonneg (g.regularLevelArea_nonneg hfs _) (Real.sqrt_nonneg _)
  · intro s t hps htz hst H hH
    have hsub : Icc s t ⊆ Ioo (f p) (f z) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2]
    exact D.integral_comp_potential_slab_of_levelArea_ratio hfs
      (isClosed_Icc.preimage hf.continuous).isCompact
      (fun x hx => hreg x (hsub hx)) (fun x _ => hQ x)
      (fun u hu => hc u (hsub hu)) hH

end PoincareConjecture.LeviCivitaData
