import PoincareConjecture.Proofs.M35.Uniqueness.KillingBochner
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Curvature











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)



theorem inner_ricciSharp {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (x v w : V n) :
    g.inner x (RicciFlow.ricciSharp D x v) w = D.ricci x w v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hrepr := b.sum_repr' w
  change (∑ i, g.inner x (b i) w • b i) = w at hrepr
  have h := congrArg (fun z => DeTurckNative.intrinsicRicciBilin D x v z) hrepr
  simp only [map_sum, map_smul, smul_eq_mul, DeTurckNative.intrinsicRicciBilin_apply] at h
  change g.inner x (∑ i, D.ricci x v (b i) • b i) w = _
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [← DeTurckNative.intrinsicRicci_symm D x v w, ← h]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)



theorem killing_hessian_trace_add_ricciSharp_eq_zero {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (hkill : ∀ y a b, DeTurckNative.metricLieDerivative D X y a b = 0)
    (x : V n) :
    @Add.add (V n) inferInstance
      (∑ i, fieldHessian D X x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
      (RicciFlow.ricciSharp D x (X x)) = 0 := by
  have hpair (w : V n) :
      g.inner x (@Add.add (V n) inferInstance
        (∑ i, fieldHessian D X x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
        (RicciFlow.ricciSharp D x (X x))) w = 0 := by
    calc
      _ = g.inner x (∑ i, fieldHessian D X x
            (g.orthonormalBasis x i) (g.orthonormalBasis x i)) w +
          g.inner x (RicciFlow.ricciSharp D x (X x)) w := by
        exact congrArg (fun L => L w) ((g.euclideanCoefficients x).map_add _ _)
      _ = 0 := by
        rw [inner_ricciSharp]
        exact killing_hessian_trace_pair D X hX hkill x w
  by_contra hne
  exact (ne_of_gt (g.pos x _ hne)) (hpair _)




theorem evolving_killing_field_stationary
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 ≤ T)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t ∈ Set.Icc 0 T, ContDiff ℝ ∞ (X t))
    (hkill : ∀ t ∈ Set.Icc 0 T, ∀ x u v,
      DeTurckNative.metricLieDerivative (G.flow.connection t) (X t) x u v = 0)
    (hheat : ∀ t ∈ Set.Icc 0 T, ∀ x,
      HasDerivWithinAt (fun s => X s x)
        (@Add.add StandardCapSpace inferInstance
          (∑ i, fieldHessian (G.flow.connection t) (X t) x
          ((G.flow.metric t).orthonormalBasis x i)
          ((G.flow.metric t).orthonormalBasis x i))
          (RicciFlow.ricciSharp (G.flow.connection t) x (X t x)))
        (Set.Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : StandardCapSpace) :
    X t x = X 0 x := by
  have hz (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
      HasDerivWithinAt (fun r => X r x) 0 (Set.Icc 0 T) s := by
    simpa only [killing_hessian_trace_add_ricciSharp_eq_zero
      (G.flow.connection s) (X s) (hX s hs) (hkill s hs) x] using hheat s hs x
  have hnorm := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hz (fun s hs => by simp) ⟨le_rfl, hT⟩ ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hnorm

end PoincareConjecture.M35.Uniqueness
