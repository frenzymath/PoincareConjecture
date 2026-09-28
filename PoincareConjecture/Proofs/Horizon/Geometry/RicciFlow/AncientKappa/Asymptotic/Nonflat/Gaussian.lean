import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Integrable
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.Entropy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flat.Rigidity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle BigOperators

universe u
namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

private theorem ricci_eq_zero_of_curvatureTensorNorm_eq_zero
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (hflat : D.curvatureTensorNorm x = 0) (v w : TangentSpace (𝓡 n) x) :
    D.ricci x v w = 0 := by
  classical
  have hdiag (a : TangentSpace (𝓡 n) x) : D.ricci x a a = 0 := by
    have h := D.abs_ricci_quadratic_le_curvatureTensorNorm x a
    rw [hflat, mul_zero, zero_mul] at h
    exact abs_nonpos_iff.mp h
  let b := g.orthonormalBasis x
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x (b i) (b i)
  have hB (a c : TangentSpace (𝓡 n) x) : B a c = D.ricci x a c := by
    simp only [B, LinearMap.sum_apply,
      LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci, b]
  have h := hdiag (v + w)
  rw [← hB] at h
  simp only [map_add, LinearMap.add_apply, hB, hdiag, D.ricci_symmetric x w v] at h
  linarith

private theorem laplacian_eq_dim_mul_of_hessian_eq_metric
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (φ : M → ℝ) (c : ℝ)
    (hess : ∀ x (v w : TangentSpace (𝓡 n) x),
      D.hessian φ x v w = c * g.inner x v w) (x : M) :
    D.laplacian φ x = (n : ℝ) * c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 :=
    (g.orthonormalBasis x).inner_eq_one i
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  simp only [LeviCivitaData.laplacian, hess, hb, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]



theorem RicciFlow.integral_gaussian_of_flat_soliton_entropy
    {J : Set ℝ} (F : RicciFlow n M J) {f : M × ℝ → ℝ} {t : ℝ} (ht : t < 0)
    (hc : MetricComplete (F.metric t))
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => f (x, t)))
    (hsol : ∀ x (v w : TangentSpace (𝓡 n) x),
      (F.connection t).ricci x v w + (F.connection t).hessian (fun y => f (y, t)) x v w +
        (1 / (2 * t)) * (F.metric t).inner x v w = 0)
    (hzero : ∀ x, F.entropyFactor f t x = 0)
    (hflat : ∀ x, (F.connection t).curvatureTensorNorm x = 0) :
    (∫ x, (-t) ^ (-(n : ℝ) / 2) * Real.exp (-f (x, t))
      ∂(F.metric t).volumeMeasure) = euclideanReducedVolume n := by
  let g := F.metric t
  let D := F.connection t
  let φ := fun x => f (x, t)
  have hricci (x : M) (v w : TangentSpace (𝓡 n) x) : D.ricci x v w = 0 :=
    ricci_eq_zero_of_curvatureTensorNorm_eq_zero D x (hflat x) v w
  have hscalar (x : M) : D.scalarCurvature x = 0 := by
    simp only [LeviCivitaData.scalarCurvature, hricci, Finset.sum_const_zero]
  have hcoeff : (1 : ℝ) / (2 * t) = -(1 / (2 * (-t))) := by
    simp only [mul_neg, one_div, inv_neg, neg_neg]
  have hess (x : M) (v w : TangentSpace (𝓡 n) x) :
      D.hessian φ x v w = (1 / (2 * (-t))) * g.inner x v w := by
    have h := hsol x v w
    rw [hricci, hcoeff] at h
    dsimp only [D, g, φ]
    linarith
  have hlap (x : M) : D.laplacian φ x = (n : ℝ) / (2 * (-t)) := by
    rw [laplacian_eq_dim_mul_of_hessian_eq_metric D φ (1 / (2 * (-t))) hess x]
    ring
  have hgrad (x : M) : φ x = (-t) * g.inner x (D.gradient φ x) (D.gradient φ x) := by
    have h := hzero x
    change -t * (2 * D.laplacian φ x - g.inner x (D.gradient φ x) (D.gradient φ x) +
      D.scalarCurvature x) + φ x - n = 0 at h
    rw [hlap, hscalar] at h
    have hn : (-t) * (2 * ((n : ℝ) / (2 * (-t)))) = n := by
      field_simp [ne_of_lt ht]
    nlinarith [hn]
  let A : FlatShrinkingPotentialData (n := n) (M := M) :=
    { metric := g
      connection := D
      complete := hc
      potential := φ
      tau := -t
      tau_pos := neg_pos.mpr ht
      potential_smooth := hf
      hessian_eq := hess
      gradient_eq := hgrad
      flat := hflat }
  obtain ⟨e, he, hp, hm⟩ := A.gaussian_rigidity
  exact hm

namespace AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}




theorem nonflat_at_of_limitReducedLength_soliton_entropy
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)))
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    (hsol : ∀ t < 0, ∀ x : G.limit.carrier.carrier, ∀ v w : TangentSpace (𝓡 n) x,
      (G.limit.flow.connection t).ricci x v w +
        (G.limit.flow.connection t).hessian (fun y => l (y, -t)) x v w +
        (1 / (2 * t)) * (G.limit.flow.metric t).inner x v w = 0)
    (hzero : ∀ t < 0, ∀ x : G.limit.carrier.carrier,
      G.limit.flow.entropyFactor (fun z => l (z.1, -z.2)) t x = 0) :
    ∀ t < 0, ∃ x : G.limit.carrier.carrier,
      (G.limit.flow.connection t).curvatureTensorNorm x ≠ 0 := by
  classical
  let : ConnectedSpace G.limit.carrier.carrier :=
    { isPreconnected_univ := G.limit.carrier.connected.isPreconnected
      toNonempty := ⟨G.limit.base⟩ }
  obtain ⟨V, hV0, hVE, hmass⟩ := G.exists_integrable_constant_limitDensity_mass P
    hl.continuousOn hlim
  intro t ht
  by_contra hflat
  push Not at hflat
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => l (x, -t)) :=
    contMDiffOn_univ.mp (hl.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun x _ => ⟨mem_univ x, neg_pos.mpr ht⟩))
  have hgauss := G.limit.flow.integral_gaussian_of_flat_soliton_entropy
    (f := fun z => l (z.1, -z.2)) ht (G.limit.complete t ht) hf
    (hsol t ht) (hzero t ht) hflat
  have hm : (∫ x, (-t) ^ (-(n : ℝ) / 2) * Real.exp (-l (x, -t))
      ∂(G.limit.flow.metric t).volumeMeasure) = V := by
    simpa only [neg_neg, calibratedMetricVolume_eq_volumeMeasure] using
      (hmass (-t) (neg_pos.mpr ht)).2
  exact hVE.ne (hm.symm.trans hgauss)

end AncientCompactTimeConvergence
end PoincareConjecture
