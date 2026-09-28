import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Services
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem normalized_scalar_direction_le_gradient
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤ scalarGradientNorm g D x := by
  apply le_csSup (s := Set.range (fun w :
    {w : TangentSpace (𝓡 3) x // g.inner x w w = 1} =>
      |mvfderiv (𝓡 3) D.scalarCurvature x w.1|)) ?_ ⟨⟨v, hv⟩, rfl⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine ⟨‖mvfderiv (𝓡 3) D.scalarCurvature x‖, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hw : ‖w.1‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner x w.1 w.1) = 1
    rw [w.2, Real.sqrt_one]
  simpa only [Real.norm_eq_abs, hw, mul_one] using
    (mvfderiv (𝓡 3) D.scalarCurvature x).le_opNorm w.1

variable [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b : ℝ}

namespace AncientKappaNormalization



theorem scalarGradientNorm_le (N : AncientKappaNormalization K p b)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrad : scalarGradientNorm (N.target.flow.metric 0)
      (N.target.flow.connection 0) p ≤ B) :
    scalarGradientNorm (K.flow.metric b) (K.flow.connection b) p ≤
      B * (K.flow.connection b).scalarCurvature p ^ (3 / 2 : ℝ) := by
  have hq : 0 < Real.sqrt N.scale := Real.sqrt_pos.mpr N.scale_pos
  have hfun : (K.flow.connection b).scalarCurvature =
      fun x => N.scale * (N.target.flow.connection 0).scalarCurvature x := by
    funext x
    have h := N.scalar_eq 0 le_rfl x
    calc
      _ = (K.flow.connection (b + 0 / N.scale)).scalarCurvature x :=
        congrArg (fun t => (K.flow.connection t).scalarCurvature x) (by simp)
      _ = _ := by simpa only [mul_comm] using ((eq_div_iff N.scale_pos.ne').mp h).symm
  have hpow : N.scale ^ (3 / 2 : ℝ) = N.scale * Real.sqrt N.scale := by
    calc
      _ = N.scale ^ (1 + 1 / 2 : ℝ) := by norm_num
      _ = _ := by rw [Real.rpow_add N.scale_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [← N.scale_eq, hpow]
  unfold scalarGradientNorm
  by_cases hne : (Set.range (fun v :
      {v : TangentSpace (𝓡 3) p // (K.flow.metric b).inner p v v = 1} =>
        |mvfderiv (𝓡 3) (K.flow.connection b).scalarCurvature p v.1|)).Nonempty
  · apply csSup_le hne
    rintro _ ⟨v, rfl⟩
    let w : TangentSpace (𝓡 3) p := (Real.sqrt N.scale)⁻¹ • v.1
    have hw : (N.target.flow.metric 0).inner p w w = 1 := by
      rw [N.metric_eq]
      simp only [zero_div, add_zero, w, map_smul, smul_apply, smul_eq_mul, v.2]
      have hs := Real.sq_sqrt N.scale_pos.le
      field_simp
      nlinarith
    have hd : mvfderiv (𝓡 3) (K.flow.connection b).scalarCurvature p v.1 =
        (N.scale * Real.sqrt N.scale) *
          mvfderiv (𝓡 3) (N.target.flow.connection 0).scalarCurvature p w := by
      rw [hfun, mvfderiv_const_mul]
      simp only [w, map_smul, smul_eq_mul]
      field_simp
    change |mvfderiv (𝓡 3) (K.flow.connection b).scalarCurvature p v.1| ≤ _
    rw [hd, abs_mul, abs_of_pos (mul_pos N.scale_pos hq)]
    calc
      _ ≤ (N.scale * Real.sqrt N.scale) * B :=
        mul_le_mul_of_nonneg_left
          ((normalized_scalar_direction_le_gradient _ _ p w hw).trans hgrad)
          (mul_nonneg N.scale_pos.le hq.le)
      _ = _ := mul_comm _ _
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact mul_nonneg hB (mul_nonneg N.scale_pos.le hq.le)


theorem scalar_derivative_eq (N : AncientKappaNormalization K p b)
    (hb : b ≤ 0) {d d' : ℝ}
    (hd : HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature p)
      d (Set.Iic 0) b)
    (hd' : HasDerivWithinAt (fun s => (N.target.flow.connection s).scalarCurvature p)
      d' (Set.Iic 0) 0) :
    d = N.scale ^ 2 * d' := by
  have hclock : HasDerivWithinAt (fun s : ℝ => b + s / N.scale)
      (1 / N.scale) (Set.Iic 0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const N.scale).const_add b).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun s : ℝ => b + s / N.scale) (Set.Iic 0) (Set.Iic 0) := by
    intro s hs
    exact add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs N.scale_pos.le)
  have hdcomp := (hd.comp_of_eq 0 hclock hmaps (by simp)).div_const N.scale
  have htarget : HasDerivWithinAt
      (fun s => (N.target.flow.connection s).scalarCurvature p)
      (d * (1 / N.scale) / N.scale) (Set.Iic 0) 0 :=
    hdcomp.congr_of_mem (fun s hs => N.scalar_eq s hs p) (by simp)
  have heq := (uniqueDiffOn_Iic (0 : ℝ) 0 (by simp)).eq_deriv (Set.Iic 0) htarget hd'
  field_simp [N.scale_pos.ne'] at heq
  nlinarith



theorem scalarEvolution_bound (N : AncientKappaNormalization K p b)
    (S : ScalarDerivativeServices.{u}) (hb : b ≤ 0) {B : ℝ}
    (hderiv : |(N.target.flow.connection 0).laplacian
        (N.target.flow.connection 0).scalarCurvature p +
        2 * (N.target.flow.connection 0).ricciNormSq p| ≤ B) :
    |(K.flow.connection b).laplacian (K.flow.connection b).scalarCurvature p +
        2 * (K.flow.connection b).ricciNormSq p| ≤
      B * (K.flow.connection b).scalarCurvature p ^ 2 := by
  rw [N.scalar_derivative_eq hb
    (S.scalar_evolution M (Set.Iic 0) K.flow b hb p)
    (S.scalar_evolution M (Set.Iic 0) N.target.flow 0 (by simp) p),
    abs_mul, abs_of_nonneg (sq_nonneg N.scale), ← N.scale_eq]
  exact (mul_le_mul_of_nonneg_left hderiv (sq_nonneg N.scale)).trans_eq (mul_comm _ _)


theorem scalarDerivWithin_bound (N : AncientKappaNormalization K p b)
    (S : ScalarDerivativeServices.{u}) (hb : b ≤ 0) {B : ℝ}
    (hderiv : |(N.target.flow.connection 0).laplacian
        (N.target.flow.connection 0).scalarCurvature p +
        2 * (N.target.flow.connection 0).ricciNormSq p| ≤ B) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature p)
        d (Set.Iic 0) b ∧
      |d| ≤ B * (K.flow.connection b).scalarCurvature p ^ 2 :=
  ⟨_, S.scalar_evolution M (Set.Iic 0) K.flow b hb p,
    N.scalarEvolution_bound S hb hderiv⟩

end AncientKappaNormalization
end PoincareConjecture
