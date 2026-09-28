import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Harnack
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Path.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

private theorem ancient_path_energy_le_distance
    {K : AncientKappaSolution n M} (A : AncientKappaStructuralData K)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M) :
    ∃ η : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 η (Icc a b) ∧
      η a = x ∧ η b = y ∧
      spacetimeEnergy K.flow η a b ≤ ((K.flow.metric a).edist x y).toReal ^ 2 / (b - a) := by
  let g := K.flow.metric a
  let R := (g.edist x x).toReal + (g.edist x y).toReal + 1
  obtain ⟨γ, hγ, hγ0, hγ1, _, hspeed⟩ :=
    g.exists_heat_harnack_path (K.complete a (hab.le.trans hb)) x x y
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
    K.flow hab (fun t ht => ht.2.trans hb) η hη
  calc
    spacetimeEnergy K.flow η a b ≤ ∫ _t in a..b, (g.edist x y).toReal ^ 2 / δ ^ 2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab.le hint intervalIntegrable_const
      intro t ht
      exact (A.metric_monotone a t ht.1.le (ht.2.le.trans hb)
        (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1)).trans_eq (hspeedη t ht)
    _ = ((K.flow.metric a).edist x y).toReal ^ 2 / (b - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      change δ * ((g.edist x y).toReal ^ 2 / δ ^ 2) = (g.edist x y).toReal ^ 2 / δ
      field_simp

namespace AncientAsymptoticSolitonPredecessors

theorem scalar_le_exp_distance {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) (x y : M) :
    (K.flow.connection a).scalarCurvature x ≤ (K.flow.connection b).scalarCurvature y *
      Real.exp (((K.flow.metric a).edist x y).toReal ^ 2 / (2 * (b - a))) := by
  obtain ⟨C⟩ := P.structural
  let A := C.structural M K
  obtain ⟨η, hη, hηa, hηb, henergy⟩ := ancient_path_energy_le_distance A hab hb x y
  have hi := P.harnack.ancient_integrated n M K.flow K.complete
    K.nonnegative_curvature_operator K.harnack_operator_bound K.nonflat
    a b hab hb η hη x y hηa hηb
  have hfirst : (K.flow.connection a).scalarCurvature x ≤
      (K.flow.connection b).scalarCurvature y * Real.exp (spacetimeEnergy K.flow η a b / 2) := by
    have hh := mul_le_mul_of_nonneg_right hi (Real.exp_pos (spacetimeEnergy K.flow η a b / 2)).le
    have he : Real.exp (-spacetimeEnergy K.flow η a b / 2) *
        Real.exp (spacetimeEnergy K.flow η a b / 2) = 1 := by
      rw [← Real.exp_add,
        show -spacetimeEnergy K.flow η a b / 2 + spacetimeEnergy K.flow η a b / 2 = 0 by ring,
        Real.exp_zero]
    simpa only [mul_assoc, he, mul_one] using hh
  apply hfirst.trans
  apply mul_le_mul_of_nonneg_left _ (A.scalar_pos b hb y).le
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_right henergy (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [div_div, mul_comm (b - a) 2] using h

theorem curvature_le_scalar_exp_on_two_time_ball {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K)
    {s t a b r : ℝ} (hs : s ≤ a) (ht : t ≤ a) (hab : a < b) (hb : b ≤ 0)
    (p x : M) (hx : x ∈ (K.flow.metric s).ball p r) :
    (K.flow.connection t).curvatureTensorNorm x ≤
      (K.flow.connection b).scalarCurvature p * Real.exp (r ^ 2 / (2 * (b - a))) := by
  obtain ⟨C⟩ := P.structural
  let A := C.structural M K
  let q := max s t
  have hqa : q ≤ a := max_le hs ht
  have hqb : q < b := hqa.trans_lt hab
  have hq0 : q ≤ 0 := hqb.le.trans hb
  have hdist : ((K.flow.metric q).edist x p).toReal ≤ r := by
    have hsm : (K.flow.metric s).edist p x < ENNReal.ofReal r := hx
    have hqm : (K.flow.metric q).edist p x < ENNReal.ofReal r :=
      (A.edist_monotone s q (le_max_left s t) hq0 p x).trans_lt hsm
    have hsym : (K.flow.metric q).edist x p = (K.flow.metric q).edist p x := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨(K.flow.metric q).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hsym]
    exact (ENNReal.toReal_lt_of_lt_ofReal hqm).le
  calc
    (K.flow.connection t).curvatureTensorNorm x ≤ (K.flow.connection q).scalarCurvature x :=
      A.past_norm_le_scalar t q (le_max_right s t) hq0 x
    _ ≤ (K.flow.connection b).scalarCurvature p *
        Real.exp (((K.flow.metric q).edist x p).toReal ^ 2 / (2 * (b - q))) :=
      P.scalar_le_exp_distance hqb hb x p
    _ ≤ (K.flow.connection b).scalarCurvature p * Real.exp (r ^ 2 / (2 * (b - a))) := by
      apply mul_le_mul_of_nonneg_left _ (A.scalar_pos b hb p).le
      apply Real.exp_le_exp.mpr
      apply (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ ENNReal.toReal_nonneg hdist 2) (by positivity : 0 ≤ 2 * (b - q))).trans
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by linarith)

end AncientAsymptoticSolitonPredecessors

namespace AncientRescaling

theorem curvature_le_scalar_exp_on_two_time_ball
    {K : AncientKappaSolution n M} {τ : ℝ} (R : AncientRescaling K τ)
    (P : AncientAsymptoticSolitonPredecessors K)
    {s t a b r : ℝ} (hs : s ≤ a) (ht : t ≤ a) (hab : a < b) (hb : b < 0)
    (p x : M) (hx : x ∈ (R.flow.metric s).ball p r) :
    (R.flow.connection t).curvatureTensorNorm x ≤
      (R.flow.connection b).scalarCurvature p * Real.exp (r ^ 2 / (2 * (b - a))) := by
  let q := Real.sqrt (1 / τ)
  have hq : 0 < q := Real.sqrt_pos.mpr (one_div_pos.mpr R.tau_pos)
  have hq2 : q ^ 2 = 1 / τ := Real.sq_sqrt (one_div_pos.mpr R.tau_pos).le
  have hs0 : s < 0 := (hs.trans_lt hab).trans hb
  have ht0 : t < 0 := (ht.trans_lt hab).trans hb
  have hball : (K.flow.metric (τ * s)).ball p (r / q) = (R.flow.metric s).ball p r := by
    simpa only [q, mul_div_cancel₀ r hq.ne'] using (R.ball_scale s hs0 p (r / q)).symm
  have hbound := P.curvature_le_scalar_exp_on_two_time_ball
    (mul_le_mul_of_nonneg_left hs R.tau_pos.le)
    (mul_le_mul_of_nonneg_left ht R.tau_pos.le)
    (mul_lt_mul_of_pos_left hab R.tau_pos)
    (mul_neg_of_pos_of_neg R.tau_pos hb).le p x (hball.symm ▸ hx)
  have hexp : (r / q) ^ 2 / (2 * (τ * b - τ * a)) = r ^ 2 / (2 * (b - a)) := by
    rw [div_pow, hq2, ← mul_sub]
    field_simp [R.tau_pos.ne', (sub_pos.mpr hab).ne']
  rw [hexp] at hbound
  rw [R.curvature_norm_scale t ht0 x, R.scalar_scale b hb p]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound R.tau_pos.le

end AncientRescaling

end PoincareConjecture
