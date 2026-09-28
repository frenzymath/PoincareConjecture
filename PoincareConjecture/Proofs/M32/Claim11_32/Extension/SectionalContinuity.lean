import PoincareConjecture.Definitions.Ch04.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.Rayleigh
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

open RicciFlowAnalysis

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 X}

private theorem sectional_changeBasis (D : LeviCivitaData g) (x : X)
    (u v : TangentSpace (𝓡 3) x) (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    D.sectionalCurvature x (a • u + b • v) (c • u + d • v) =
      D.sectionalCurvature x u v := by
  have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
    simp only [D.curvatureTensor_add_first, D.curvatureTensor_add_second,
      D.curvatureTensor_add_third, D.curvatureTensor_add_last,
      D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
      D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
      D.curvatureTensor_zero_first, D.curvatureTensor_zero_last]
    simp only [D.curvatureTensor_swap_first x v u,
      D.curvatureTensor_swap_last x u v v u]
    ring
  have hgram : metricGram g x (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * metricGram g x u v := by
    simp only [metricGram, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      g.symm x v u]
    ring
  change _ / metricGram g x _ _ = _ / metricGram g x _ _
  rw [hnum, hgram]
  field_simp [hdet]

private theorem orthonormalPair_linearIndependent (x : X)
    (u v : TangentSpace (𝓡 3) x) (huv : LeviCivitaData.IsOrthonormalPair g x u v) :
    LinearIndependent ℝ ![u, v] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have horth : Orthonormal ℝ (![u, v] : Fin 2 → TangentSpace (𝓡 3) x) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact huv.1
    · exact huv.2.2
    · change inner ℝ v u = 0
      rw [real_inner_comm]
      exact huv.2.2
    · exact huv.2.1
  exact horth.linearIndependent

private theorem sectional_values_eq_model_image (D : LeviCivitaData g) (x : X)
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] TangentSpace (𝓡 3) x) :
    {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v} =
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        D.sectionalCurvature x (e p.1) (e p.2)) '' modelOrthonormalPairs 3 := by
  ext k
  constructor
  · rintro ⟨u, v, huv, hk⟩
    have hlin := (orthonormalPair_linearIndependent x u v huv).map'
      e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
    have hlin' : LinearIndependent ℝ ![e.symm u, e.symm v] := by
      convert! hlin using 1
      ext i
      fin_cases i <;> rfl
    obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ :=
      LeviCivitaData.exists_orthonormal_changeBasis (e.symm u) (e.symm v) hlin'
    refine ⟨(a • e.symm u + b • e.symm v, c • e.symm u + d • e.symm v), ?_, ?_⟩
    · refine ⟨?_, ?_, hpq⟩
      · nlinarith [real_inner_self_eq_norm_sq (a • e.symm u + b • e.symm v),
          norm_nonneg (a • e.symm u + b • e.symm v)]
      · nlinarith [real_inner_self_eq_norm_sq (c • e.symm u + d • e.symm v),
          norm_nonneg (c • e.symm u + d • e.symm v)]
    · simp only [map_add, map_smul, e.apply_symm_apply]
      rw [sectional_changeBasis D x u v a b c d hdet]
      simp only [LeviCivitaData.sectionalCurvature, huv.1, huv.2.1, huv.2.2,
        one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, div_one]
      exact hk.symm
  · rintro ⟨⟨p, q⟩, hpq, hk⟩
    have horth : Orthonormal ℝ (![p, q] : Fin 2 → EuclideanSpace ℝ (Fin 3)) := by
      constructor
      · intro i
        fin_cases i
        · exact hpq.1
        · exact hpq.2.1
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hpq.2.2
        · change inner ℝ q p = 0
          rw [real_inner_comm]
          exact hpq.2.2
        · exact (hij rfl).elim
    have hlin := horth.linearIndependent.map' e.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.injective)
    have hlin' : LinearIndependent ℝ ![e p, e q] := by
      convert! hlin using 1
      ext i
      fin_cases i <;> rfl
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨a, b, c, d, hdet, hu, hv, huv⟩ :=
      LeviCivitaData.exists_orthonormal_changeBasis (e p) (e q) hlin'
    refine ⟨a • e p + b • e q, c • e p + d • e q, ⟨hu, hv, huv⟩, ?_⟩
    change D.sectionalCurvature x (e p) (e q) = k at hk
    rw [← hk, ← sectional_changeBasis D x (e p) (e q) a b c d hdet]
    change _ / (inner ℝ (a • e p + b • e q) (a • e p + b • e q) *
      inner ℝ (c • e p + d • e q) (c • e p + d • e q) -
      (inner ℝ (a • e p + b • e q) (c • e p + d • e q)) ^ 2) = _
    rw [hu, hv, huv]
    norm_num

theorem flow_leastSectionalCurvature_continuousOn {J : Set ℝ}
    (G : RicciFlow 3 X J) (x : X) :
    ContinuousOn (fun t => (G.connection t).leastSectionalCurvature x) J := by
  let V := EuclideanSpace ℝ (Fin 3)
  let e := trivializationAt V (TangentSpace (𝓡 3) : X → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let L : V ≃ₗ[ℝ] TangentSpace (𝓡 3) x :=
    (e.continuousLinearEquivAt ℝ x hx).symm.toLinearEquiv
  have hL (v : V) : L v = e.symmL ℝ x v := by
    exact congrFun (e.symm_continuousLinearEquivAt_eq hx) v
  let P := modelOrthonormalPairs 3
  let : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs 3)
  let f (t : J) (p : P) : ℝ :=
    (G.connection t).sectionalCurvature x (e.symmL ℝ x p.1.1) (e.symmL ℝ x p.1.2)
  have hf : Continuous (Function.uncurry f) := by
    have h := (continuousOn_flow_sectionalRayleigh_trivialization G x).comp_continuous
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_const).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p : J × P => ⟨⟨p.1.property, hx⟩, p.2.property⟩)
    exact h
  have himage (t : J) : f t '' univ =
      (fun p : V × V => (G.connection t).sectionalCurvature x (L p.1) (L p.2)) '' P := by
    ext k
    constructor
    · rintro ⟨p, _, hp⟩
      exact ⟨p.1, p.2, by simpa only [f, hL] using hp⟩
    · rintro ⟨p, hp, hk⟩
      exact ⟨⟨p, hp⟩, mem_univ _, by simpa only [f, hL] using hk⟩
  have hmin := (isCompact_univ : IsCompact (univ : Set P)).continuous_sInf (f := f) hf
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hmin.congr
  intro t
  rw [himage]
  exact congrArg sInf (sectional_values_eq_model_image (G.connection t) x L).symm

theorem flow_negativeCurvaturePart_continuousOn {J : Set ℝ}
    (G : RicciFlow 3 X J) (x : X) :
    ContinuousOn (fun t => (G.connection t).negativeCurvaturePart x) J :=
  (flow_leastSectionalCurvature_continuousOn G x).neg.sup continuousOn_const

end PoincareConjecture.M32
