import PoincareConjecture.Proofs.M60.Mathlib.ParametricMetricTrace
import PoincareConjecture.Proofs.M60.Mathlib.ConformalTrace
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundVolume









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



noncomputable def m60SphereIntrinsicEnergy (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (p : UnitTwoSphere) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, g.inner (f p)
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i))
    (mfderiv (𝓡 2) (𝓡 n) f p (m60RoundSphereMetric.orthonormalBasis p i))



theorem m60SphereIntrinsicEnergy_family_contMDiffAt (g : RiemannianMetric n M)
    (v : ℝ × UnitTwoSphere → M) (q : ℝ × UnitTwoSphere)
    (hv : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ v q) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun r => m60SphereIntrinsicEnergy g (fun p => v (r.1, p)) r.2) q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  let F := fun (r : ℝ × UnitTwoSphere) (p : UnitTwoSphere) => v (r.1, p)
  let A := fun r : ℝ × UnitTwoSphere =>
    (M60.metricPullbackForm (n := 2) g (F r) r.2).toBilinForm
  have hF : ContMDiffAt (((𝓘(ℝ, ℝ)).prod (𝓡 2)).prod (𝓡 2)) (𝓡 n) ∞
      (Function.uncurry F) (q, q.2) :=
    hv.comp (q, q.2) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  apply contMDiffAt_const.mul
  apply M60.contMDiffAt_metricTrace_along m60RoundSphereMetric
    (fun r : ℝ × UnitTwoSphere => r.2) contMDiffAt_snd A
  intro V W hV hW
  exact (M60.contMDiffAt_parametric_tangentMap F Prod.snd hF contMDiffAt_snd V hV).inner_bundle
    (M60.contMDiffAt_parametric_tangentMap F Prod.snd hF contMDiffAt_snd W hW)



theorem m60SphereIntrinsicEnergy_contMDiff (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (m60SphereIntrinsicEnergy g f) := by
  intro p
  have h := m60SphereIntrinsicEnergy_family_contMDiffAt g (fun q => f q.2) (0, p)
    ((hf p).comp (0, p) contMDiffAt_snd)
  exact h.comp p (contMDiffAt_const.prodMk contMDiffAt_id)



theorem m60SphereEnergyDensity_eq_intrinsic_mul (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (z : LoopPlane) :
    m60SphereEnergyDensity g f z =
      m60SphereIntrinsicEnergy g f (m60SphereParameter z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨m60RoundSphereMetric.toRiemannianMetric⟩
  let p := m60SphereParameter z
  let w := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let B := (M60.metricPullbackForm (n := 2) g f p).toBilinForm
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) p) := by
    unfold TangentSpace
    infer_instance
  have hw (i j : Fin 2) : inner ℝ (w i) (w j) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * (if i = j then 1 else 0) := by
    change m60RoundSphereInner p (w i) (w j) = _
    rw [m60SphereParameter_inner, (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite]
  have htrace := M60.sum_bilinear_conformal_basis B
    (m60RoundSphereMetric.orthonormalBasis p) w
    (by change 2 = Module.finrank ℝ LoopPlane; simp) (by positivity) hw
  have hleft : m60SphereEnergyDensity g f z = (1 / 2 : ℝ) * ∑ i, B (w i) (w i) := by
    unfold m60SphereEnergyDensity m60EnergyDensity
    rw [Matrix.trace_fin_two]
    unfold m60AreaGram
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
    simp only [B, ContinuousLinearMap.toBilinForm_apply, M60.metricPullbackForm_apply,
      w, p, Fin.sum_univ_two]
    rfl
  rw [hleft, htrace]
  simp only [B, ContinuousLinearMap.toBilinForm_apply, M60.metricPullbackForm_apply,
    m60SphereIntrinsicEnergy, p]
  ring



theorem m60SphereEnergy_eq_intrinsic_integral (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    m60SphereEnergy g f =
      ∫ p, m60SphereIntrinsicEnergy g f p ∂m60RoundSphereMetric.volumeMeasure := by
  rw [m60RoundSphereMetric_integral _ (m60SphereIntrinsicEnergy_contMDiff g f hf).continuous]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    m60SphereEnergyDensity_eq_intrinsic_mul g f (hf.of_le (by simp)) z

end PoincareConjecture
