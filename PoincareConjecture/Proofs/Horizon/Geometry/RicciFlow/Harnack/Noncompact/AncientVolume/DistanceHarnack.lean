import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_inner_self_le_of_ancient_ricci_nonneg
    (F : RicciFlow n M (Iic 0))
    (hRic : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric b).inner x v v ≤ (F.metric a).inner x v v := by
  have hsub : Icc a b ⊆ Iic (0 : ℝ) := fun _ ht => ht.2.trans hb
  have hcont : ContinuousOn (fun t => (F.metric t).inner x v v) (Icc a b) := by
    intro t ht
    exact (F.equation t (hsub ht) x v v).continuousWithinAt.mono hsub
  have hderiv (t : ℝ) (ht : t ∈ interior (Icc a b)) :
      HasDerivAt (fun s => (F.metric s).inner x v v)
        (-2 * (F.connection t).ricci x v v) t := by
    have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    exact (F.equation t (ht'.2.le.trans hb) x v v).hasDerivAt
      (Iic_mem_nhds (ht'.2.trans_le hb))
  have hmono : AntitoneOn (fun t => (F.metric t).inner x v v) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hderiv t ht).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (hRic t (hsub (interior_subset ht)) x v)
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

private theorem exists_path_spacetimeEnergy_le_distance
    [T3Space M] [PreconnectedSpace M]
    (F : RicciFlow n M (Iic 0))
    (hRic : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0)
    (hcomplete : MetricComplete (F.metric a)) (x y : M) :
    ∃ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 η (Icc a b) ∧
      η a = x ∧ η b = y ∧
      spacetimeEnergy F η a b ≤ ((F.metric a).edist x y).toReal ^ 2 / (b - a) := by
  let g := F.metric a
  let R := (g.edist x x).toReal + (g.edist x y).toReal + 1
  obtain ⟨γ, hγ, hγ0, hγ1, _, hspeed⟩ :=
    g.exists_heat_harnack_path hcomplete x x y
      (show (g.edist x x).toReal ≤ R by
        dsimp [R]; linarith [ENNReal.toReal_nonneg (a := g.edist x y)])
      (show (g.edist x y).toReal ≤ R by
        dsimp [R]; linarith [ENNReal.toReal_nonneg (a := g.edist x x)])
  let δ := b - a
  have hδ : 0 < δ := sub_pos.mpr hab
  let z : ℝ → ℝ := fun t => (t - a) / δ
  let η : ℝ → M := γ ∘ z
  have hz : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 z := by
    apply contMDiff_iff_contDiff.mpr
    dsimp only [z]
    fun_prop
  have hmap : MapsTo z (Icc a b) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hδ.le,
      (div_le_one hδ).mpr (sub_le_sub_right ht.2 a)⟩
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 η (Icc a b) :=
    hγ.comp hz.contMDiffOn hmap
  have hηa : η a = x := by simp only [η, Function.comp_apply, z, sub_self, zero_div, hγ0]
  have hηb : η b = y := by
    simp only [η, Function.comp_apply, z, ← show δ = b - a from rfl, div_self hδ.ne', hγ1]
  refine ⟨η, hη, hηa, hηb, ?_⟩
  have hspeedη (t : ℝ) (ht : t ∈ Ioo a b) :
      g.inner (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1) = (g.edist x y).toReal ^ 2 / δ ^ 2 := by
    have hzt : z t ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (sub_pos.mpr ht.1) hδ,
        (div_lt_one hδ).mpr (sub_lt_sub_right ht.2 a)⟩
    have hγt := (hγ (z t) (Ioo_subset_Icc_self hzt)).contMDiffAt (Icc_mem_nhds hzt.1 hzt.2)
    have hzd : HasDerivAt z δ⁻¹ t := by
      simpa only [z, id_eq, one_div] using ((hasDerivAt_id t).sub_const a).div_const δ
    have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1 =
        δ⁻¹ • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (z t) 1 := by
      rw [show η = γ ∘ z from rfl, mfderiv_comp_apply t
        (hγt.mdifferentiableAt one_ne_zero) (hz.mdifferentiable one_ne_zero t),
        mfderiv_eq_fderiv, hzd.hasFDerivAt.fderiv]
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (z t)) ((1 : ℝ) • δ⁻¹) =
        δ⁻¹ • (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (z t)) 1
      rw [one_smul, ← map_smul, smul_eq_mul, mul_one]
    rw [hvelocity]
    simp only [map_smul, smul_apply, smul_eq_mul]
    change δ⁻¹ * (δ⁻¹ * g.inner (γ (z t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (z t) 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (z t) 1)) = _
    rw [hspeed (z t) (Ioo_subset_Icc_self hzt)]
    field_simp
  have hint := Poincare.Geometry.RicciFlow.Harnack.intervalIntegrable_spacetimeEnergy_integrand
    F hab (fun t ht => ht.2.trans hb) η hη
  calc
    spacetimeEnergy F η a b ≤ ∫ _t in a..b, (g.edist x y).toReal ^ 2 / δ ^ 2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab.le hint intervalIntegrable_const
      intro t ht
      exact (F.metric_inner_self_le_of_ancient_ricci_nonneg hRic ht.1.le
        (ht.2.le.trans hb) (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1)).trans_eq (hspeedη t ht)
    _ = ((F.metric a).edist x y).toReal ^ 2 / (b - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      change δ * ((g.edist x y).toReal ^ 2 / δ ^ 2) = (g.edist x y).toReal ^ 2 / δ
      field_simp

variable [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]

theorem scalarCurvature_le_exp_distance_of_bounded_ancient
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M) :
    (F.connection a).scalarCurvature x ≤ (F.connection b).scalarCurvature y *
      Real.exp (((F.metric a).edist x y).toReal ^ 2 / (2 * (b - a))) := by
  have hRic : ∀ t ≤ 0, ∀ z : M, ∀ v : TangentSpace (𝓡 n) z,
      0 ≤ (F.connection t).ricci z v v := by
    intro t ht z v
    exact ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) z (hoperator t ht z) v).1
  obtain ⟨η, hη, hηa, hηb, henergy⟩ :=
    F.exists_path_spacetimeEnergy_le_distance hRic hab hb (hcomplete a (hab.le.trans hb)) x y
  have hi := Poincare.Geometry.RicciFlow.Harnack.ancient_integrated_of_differential
    hC F hoperator (F.ancient_differential_of_bounded_ancient hC hcomplete hoperator hK hbound)
    hab hb η hη hηa hηb
  have hfirst : (F.connection a).scalarCurvature x ≤ (F.connection b).scalarCurvature y *
      Real.exp (spacetimeEnergy F η a b / 2) := by
    have hh := mul_le_mul_of_nonneg_right hi (Real.exp_pos (spacetimeEnergy F η a b / 2)).le
    have he : Real.exp (-spacetimeEnergy F η a b / 2) *
        Real.exp (spacetimeEnergy F η a b / 2) = 1 := by
      rw [← Real.exp_add,
        show -spacetimeEnergy F η a b / 2 + spacetimeEnergy F η a b / 2 = 0 by ring,
        Real.exp_zero]
    simpa only [mul_assoc, he, mul_one] using hh
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _
    (F.scalarCurvature_pos_of_bounded_ancient hC hcomplete hoperator hK hbound hnonflat b hb y).le
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_right henergy (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [div_div, mul_comm (b - a) 2] using h

theorem scalarCurvature_le_exp_of_bounded_ancient_distance_le
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p)
    {a b D : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M)
    (hD : ((F.metric a).edist x y).toReal ≤ D) :
    (F.connection a).scalarCurvature x ≤ (F.connection b).scalarCurvature y *
      Real.exp (D ^ 2 / (2 * (b - a))) := by
  apply (F.scalarCurvature_le_exp_distance_of_bounded_ancient
    hC hcomplete hoperator hK hbound hnonflat hab hb x y).trans
  apply mul_le_mul_of_nonneg_left _
    (F.scalarCurvature_pos_of_bounded_ancient hC hcomplete hoperator hK hbound hnonflat b hb y).le
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hD 2) (by positivity)

theorem curvatureTensorNorm_le_exp_of_bounded_ancient_distance_le
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p)
    {a b D : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M)
    (hD : ((F.metric a).edist x y).toReal ≤ D) :
    (F.connection a).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 *
      ((F.connection b).scalarCurvature y * Real.exp (D ^ 2 / (2 * (b - a)))) := by
  apply ((F.connection a).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus n M (F.metric a) (F.connection a)) x
    (hoperator a (hab.le.trans hb) x)).trans
  exact mul_le_mul_of_nonneg_left
    (F.scalarCurvature_le_exp_of_bounded_ancient_distance_le
      hC hcomplete hoperator hK hbound hnonflat hab hb x y hD) (sq_nonneg _)

end PoincareConjecture.RicciFlow
