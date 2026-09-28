import PoincareConjecture.Proofs.M10.WeightedRays









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exponentialSliceChart_contMDiff (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (exponentialSliceChart G τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := (metricCoordinates (F.metric T) p).toContinuousLinearEquiv
  have heq : (exponentialSliceChart G τ : EuclideanSpace ℝ (Fin n) → M) =
      (fun x ↦ G.gamma (β x) τ) := funext (exponentialSliceChart_apply G τ)
  rw [heq]
  intro x
  have hz : (β x, τ) ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  exact hγ.comp x (β.toContinuousLinearMap.contMDiff.contMDiffAt.prodMk contMDiffAt_const)


theorem exponentialSliceJacobian_continuous (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Continuous (exponentialSliceJacobian G τ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact pullbackJacobian_continuousAt _
    ((exponentialSliceChart_contMDiff G hτ hmax x).of_le (by simp))

set_option backward.isDefEq.respectTransparency false in

theorem exponentialAction_continuous (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦
      G.toLExponentialFamily.action (metricCoordinates (F.metric T) p x) τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : (β x, τ) ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hact := (G.action_smooth.contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).continuousAt
  exact hact.comp (f := fun y : EuclideanSpace ℝ (Fin n) ↦ (β y, τ))
    (β.continuous.continuousAt.prodMk continuousAt_const)


theorem weightedExponentialJacobian_continuous (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Continuous (weightedExponentialJacobian G τ) := by
  have ha := exponentialAction_continuous G hτ hmax
  have hexp := Real.continuous_exp.comp (ha.div_const (2 * Real.sqrt τ)).neg
  change Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦
    Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-(G.toLExponentialFamily.action (metricCoordinates (F.metric T) p x) τ /
        (2 * Real.sqrt τ))) * exponentialSliceJacobian G τ x)
  exact (hexp.const_mul (Real.rpow τ (-(n : ℝ) / 2))).mul
    (exponentialSliceJacobian_continuous G hτ hmax)

end PoincareConjecture.M10
