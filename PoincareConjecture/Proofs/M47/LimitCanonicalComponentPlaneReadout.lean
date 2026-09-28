import PoincareConjecture.Proofs.M47.CanonicalComponentSectionalStability
import PoincareConjecture.Proofs.M34.Standard.LocalPullbackRealization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PullbackPlane

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M04 M44 SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance componentPlaneDualNormedGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance componentPlaneDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
noncomputable local instance componentPlaneCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance componentPlaneCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
private theorem partial_derivative_invertible
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞) {x : E} (hx : x ∈ f.source) :
    (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible :=
  ⟨(f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩

private theorem model_pair_independent {p : E × E} (hp : p ∈ modelOrthonormalPairs 3) :
    LinearIndependent ℝ ![p.1, p.2] := by
  have horth : Orthonormal ℝ (![p.1, p.2] : Fin 2 → E) := by
    constructor
    · intro i
      fin_cases i
      · exact hp.1
      · exact hp.2.1
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hp.2.2
      · change inner ℝ p.2 p.1 = 0
        rw [real_inner_comm]
        exact hp.2.2
      · exact (hij rfl).elim
  exact horth.linearIndependent

theorem limitCanonical_component_model_jet_lower
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {x : E} (hx : x ∈ f.source) (a : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 3) (f x),
      LeviCivitaData.IsOrthonormalPair g (f x) u v → a < D.sectionalCurvature (f x) u v)
    (p : E × E) (hp : p ∈ modelOrthonormalPairs 3) :
    metricTwoJet (g.pullbackCoefficients f) x ∈ sectionalJetLowerRegion a p.1 p.2 := by
  let L := mfderiv (𝓡 3) (𝓡 3) f x
  have hinv := partial_derivative_invertible f hx
  have hlin : LinearIndependent ℝ ![L p.1, L p.2] := by
    have h := (model_pair_independent hp).map' L.toLinearMap
      (LinearMap.ker_eq_bot.mpr hinv.injective)
    convert! h using 1
    funext i
    fin_cases i <;> rfl
  have hgram : 0 < metricGram g (f x) (L p.1) (L p.2) :=
    metricGram_pos_of_linearIndependent g (f x) _ _ hlin
  have hbound := Proofs.M47.sectional_lower_on_independent_pair D (f x) a hsec
    (L p.1) (L p.2) hlin
  refine ⟨g.isInvertible_pullbackCoefficients hinv.injective, hgram, ?_⟩
  rw [jetCurvature_pullbackCoefficients g D f.open_source f.contMDiffOn_toFun
    (fun y hy => partial_derivative_invertible f hy) hx]
  exact (lt_div_iff₀ hgram).mp hbound

omit [T2Space M] in

theorem limitCanonical_component_all_planes_of_model_jets
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {x : E} (hx : x ∈ f.source) (a : ℝ)
    (hJ : ∀ p ∈ modelOrthonormalPairs 3,
      metricTwoJet (g.pullbackCoefficients f) x ∈ sectionalJetLowerRegion a p.1 p.2) :
    ∀ u v : TangentSpace (𝓡 3) (f x),
      a * metricGram g (f x) u v ≤ D.curvatureTensor (f x) u v u v := by
  obtain ⟨gE, DE, W, hW, hxW, hWsource, hcoeff⟩ :=
    g.exists_local_immersive_pullback_realization f f.open_source hx f.contMDiffOn_toFun
      (fun y hy => (partial_derivative_invertible f hy).injective)
  have hgerm : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hW.mem_nhds hxW) hcoeff
  have htwo : metricTwoJet gE.euclideanCoefficients x =
      metricTwoJet (g.pullbackCoefficients f) x := by
    simp only [metricTwoJet, hgerm.eq_of_nhds, hgerm.fderiv_eq,
      (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hnative (p : E × E) (hp : p ∈ modelOrthonormalPairs 3) :
      a * metricGram gE x p.1 p.2 ≤ DE.curvatureTensor x p.1 p.2 p.1 p.2 := by
    have h := (hJ p hp).2.2.le
    rw [← htwo, jetCurvature_metricTwoJet DE] at h
    exact h
  have hall (u v : E) : a * metricGram gE x u v ≤ DE.curvatureTensor x u v u v := by
    apply Proofs.M46.sectional_lower_from_model_pairs DE x x ?_ a ?_ u v
    · rw [TangentBundle.trivializationAt_baseSet]
      exact mem_chart_source E x
    · intro p hp
      simp only [TangentBundle.symmL_model_space]
      exact hnative p hp
  have hmetric (y : E) (hy : y ∈ W) (u v : E) :
      gE.inner y u v = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v) :=
    congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B u v) (hcoeff y hy)
  have hcurv (u w v z : E) := DE.curvatureTensor_eq_of_local_isometry D hW
    (f.contMDiffOn_toFun.mono hWsource) hmetric hxW u w v z
  intro u v
  obtain ⟨u', rfl⟩ := (partial_derivative_invertible f hx).surjective u
  obtain ⟨v', rfl⟩ := (partial_derivative_invertible f hx).surjective v
  have h := hall u' v'
  rw [hcurv] at h
  simpa only [metricGram, hmetric x hxW] using h

omit [T2Space M] in

theorem limitCanonical_component_curvature_of_model_jets
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {x : E} (hx : x ∈ f.source) (a : ℝ)
    (hJ : ∀ p ∈ modelOrthonormalPairs 3,
      metricTwoJet (g.pullbackCoefficients f) x ∈ sectionalJetLowerRegion a p.1 p.2) :
    (∀ u v : TangentSpace (𝓡 3) (f x),
      LeviCivitaData.IsOrthonormalPair g (f x) u v → a ≤ D.sectionalCurvature (f x) u v) ∧
      6 * a ≤ D.scalarCurvature (f x) := by
  have hall := limitCanonical_component_all_planes_of_model_jets D f hx a hJ
  refine ⟨?_, Proofs.M46.scalar_lower_of_sectional_lower D (f x) a hall⟩
  intro u v huv
  have h := hall u v
  simpa only [LeviCivitaData.sectionalCurvature, metricGram, huv.1, huv.2.1,
    huv.2.2, one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one, div_one] using h

end PoincareConjecture.M47
