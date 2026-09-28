import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem pathELength_le_ofReal_halfEnergy (g : RiemannianMetric 3 M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun t =>
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) (Icc a b)) :
    g.pathELength γ a b ≤ ENNReal.ofReal
      ((∫ t in a..b, (1 / 2 : ℝ) *
        (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) ^ 2) +
          (b - a) / 2) := by
  let v : ℝ → ℝ := fun t =>
    g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
  have hv : IntervalIntegrable v volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hcont
  have hv2 : IntervalIntegrable (fun t => (1 / 2 : ℝ) * v t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.mul (hcont.pow 2)
  rw [g.pathELength_eq_ofReal_integral_speed hab hcont]
  apply ENNReal.ofReal_le_ofReal
  have h := intervalIntegral.integral_mono_on hab hv
    (hv2.add intervalIntegrable_const)
    (fun t _ => show v t ≤ (1 / 2 : ℝ) * v t ^ 2 + 1 / 2 by
      nlinarith [sq_nonneg (v t - 1)])
  rw [intervalIntegral.integral_add hv2 intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simpa only [v, smul_eq_mul, div_eq_mul_inv, one_mul] using h

theorem intrinsicOpenEDist_triangle (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {p q r : M}
    (hp : p ∈ U) (hq : q ∈ U) (hr : r ∈ U) :
    intrinsicEDist g (U : Set M) p r ≤
      intrinsicEDist g (U : Set M) p q + intrinsicEDist g (U : Set M) q r := by
  let pU : U := ⟨p, hp⟩
  let qU : U := ⟨q, hq⟩
  let rU : U := ⟨r, hr⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨(intrinsicOpenMetric g U).toRiemannianMetric⟩
  have h := Manifold.riemannianEDist_triangle (I := 𝓡 3)
    (x := pU) (y := qU) (z := rU)
  change (intrinsicOpenMetric g U).edist pU rU ≤
    (intrinsicOpenMetric g U).edist pU qU +
      (intrinsicOpenMetric g U).edist qU rU at h
  simpa only [intrinsicOpenMetric_edist, pU, qU, rU] using h

theorem intrinsicEDist_le_ofReal_prefix_halfEnergy
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {p : M} (hp : p ∈ U) {γ : ℝ → M} {a b A : ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) (U : Set M))
    (hcont : ContinuousOn (fun t =>
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) (Icc a b))
    (hprefix : intrinsicEDist g (U : Set M) p (γ a) = ENNReal.ofReal A) :
    intrinsicEDist g (U : Set M) p (γ b) ≤ ENNReal.ofReal
      (A + ((∫ t in a..b, (1 / 2 : ℝ) *
        (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) ^ 2) +
          (b - a) / 2)) := by
  have henergy : 0 ≤ (∫ t in a..b, (1 / 2 : ℝ) *
      (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) ^ 2) +
        (b - a) / 2 := by
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg hab (fun _ _ => by positivity)
    · positivity
  calc
    intrinsicEDist g (U : Set M) p (γ b) ≤
        intrinsicEDist g (U : Set M) p (γ a) +
          intrinsicEDist g (U : Set M) (γ a) (γ b) :=
      intrinsicOpenEDist_triangle g U hp (hγU ⟨le_rfl, hab⟩) (hγU ⟨hab, le_rfl⟩)
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal
        ((∫ t in a..b, (1 / 2 : ℝ) *
          (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) ^ 2) +
            (b - a) / 2) := by
      rw [hprefix]
      exact add_le_add (le_refl _) ((intrinsicEDist_le_pathELength g hab hγ hγU).trans
        (pathELength_le_ofReal_halfEnergy g hab hcont))
    _ = _ := (ENNReal.ofReal_add hA henergy).symm

end PoincareConjecture.M28
