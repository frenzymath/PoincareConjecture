import PoincareConjecture.Proofs.M35.Uniqueness.KillingGradientEnergy
import PoincareConjecture.Proofs.M35.Uniqueness.ScalarJetLinearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem vector_heat_bernstein_subsolution
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T t K A : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht : t ∈ Ioc 0 T)
    (hK : 0 ≤ K) (hA : 1 + 324 * K * t ≤ 2 * A)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ s, ContDiff ℝ ∞ (X s))
    (hJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
      (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
        (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ico 0 G.lifetime ×ˢ univ))
    (hheat : ∀ x, HasDerivWithinAt (fun s => X s x)
      (@Add.add StandardCapSpace inferInstance
        (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
        (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Ico 0 G.lifetime) t)
    (x : StandardCapSpace) (hRm : (G.flow.connection t).curvatureTensorNorm x ≤ K) :
    let Q := fun s y => ((G.flow.metric s).tensorNorm
      ((G.flow.connection s).covariantTensorDerivative
        (killingCovector (G.flow.metric s) (X s))) y) ^ 2
    let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
    ∃ a : ℝ, HasDerivWithinAt (fun s => s * Q s x + A * q s x) a (Icc 0 T) t ∧
      a ≤ (G.flow.connection t).laplacian (fun y => t * Q t y + A * q t y) x := by
  let H := fun s => (G.flow.connection s).covariantTensorDerivative
    (killingCovector (G.flow.metric s) (X s))
  let Q := fun s y => ((G.flow.metric s).tensorNorm (H s) y) ^ 2
  let q := fun s y => (G.flow.metric s).inner y (X s y) (X s y)
  have hH (s : ℝ) : IsSmoothCovariantTensor (H s) :=
    M04.isSmoothCovariantTensor_covariantTensorDerivative _
      (isSmoothCovariantTensor_killingCovector _ _ (hX s))
  have hti : t ∈ Ioo 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have htj : t ∈ interior (Ico 0 G.lifetime) := by
    simpa only [interior_Ico] using hti
  obtain ⟨a, ha, hle⟩ := lichnerowicz_normSq_heat_le G.flow H hH htj x hK hRm
    (fun v => killingCovectorGradient_lichnerowicz_hasDerivAt G hti X hX hJoint hheat x v)
  change HasDerivAt (fun s => Q s x) a t at ha
  change a ≤ (G.flow.connection t).laplacian (Q t) x +
    (4 * (3 : ℝ) ^ 4 * K) * Q t x at hle
  norm_num at hle
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt hTlt⟩
  have hdq := vector_heat_normSq_dissipation G hT hTlt ⟨ht.1.le, ht.2⟩
    X (hX t) x ((hheat x).mono hsub)
  change HasDerivWithinAt (fun s => q s x)
    ((G.flow.connection t).laplacian (q t) x - 2 * Q t x) (Icc 0 T) t at hdq
  have hd := ((hasDerivWithinAt_id t (Icc 0 T)).mul ha.hasDerivWithinAt).add
    (hdq.const_mul A)
  refine ⟨_, hd, ?_⟩
  have hQs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t) :=
    M04.contMDiff_tensorNorm_sq _ (hH t)
  have hqs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (q t) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨(G.flow.metric t).toRiemannianMetric⟩
    exact (euclidean_field_contMDiff (hX t)).inner_bundle
      (euclidean_field_contMDiff (hX t))
  change 1 * Q t x + t * a + A * ((G.flow.connection t).laplacian (q t) x -
    2 * Q t x) ≤ (G.flow.connection t).laplacian (fun y => t * Q t y + A * q t y) x
  rw [laplacian_add_at _ (f := fun y => t * Q t y) (h := fun y => A * q t y)
    (contMDiffAt_const.mul (hQs x)) (contMDiffAt_const.mul (hqs x)),
    LeviCivitaData.laplacian_const_mul, LeviCivitaData.laplacian_const_mul]
  have hQ : 0 ≤ Q t x := sq_nonneg _
  have hfirst := mul_le_mul_of_nonneg_left hle ht.1.le
  have hsecond := mul_le_mul_of_nonneg_right hA hQ
  nlinarith only [hfirst, hsecond]

end PoincareConjecture.M35.Uniqueness
