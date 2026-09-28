import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume
import PoincareConjecture.Proofs.M36.NeckCoordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}



noncomputable def retainedNegativeChart (R : MetricSurgeryResult g0 I) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M R.output.carrier ∞ := by
  let U := I.neck.region (-I.neck.epsilon⁻¹) 0
  have hsub : U ⊆ I.neck.region (-I.neck.epsilon⁻¹) 1 :=
    fun _ hy => ⟨hy.1, hy.2.1, hy.2.2.trans zero_lt_one⟩
  have hf := R.retained_smooth.mono hsub
  have hi := R.retained_inverse_smooth.mono (image_mono hsub)
  have hleft : LeftInvOn R.retained_inverse R.collapse U :=
    fun _ hx => R.retained_left_inverse (hsub hx)
  exact {
    toFun := R.collapse
    invFun := R.retained_inverse
    source := U
    target := R.collapse '' U
    map_source' := fun _ hx => mem_image_of_mem _ hx
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      rwa [hleft hx]
    left_inv' := fun _ hx => hleft hx
    right_inv' := fun _ hy => R.retained_right_inverse (image_subset_range _ _ hy)
    open_source := M36.neck_region_isOpen I.neck _ _
    open_target := Poincare.isOpen_image_of_smooth_leftInvOn
      (M36.neck_region_isOpen I.neck _ _) hf hi hleft
    contMDiffOn_toFun := hf
    contMDiffOn_invFun := hi }

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]




theorem retained_negative_volume_eq (R : MetricSurgeryResult g0 I)
    {A : Set M} (hA : MeasurableSet A)
    (hAU : A ⊆ I.neck.region (-I.neck.epsilon⁻¹) 0) :
    calibratedMetricVolume R.metric (R.collapse '' A) = calibratedMetricVolume g A := by
  let e := retainedNegativeChart R
  have hmap : (e.toOpenPartialHomeomorph : M → R.output.carrier) = R.collapse := rfl
  have hnorm (x : M) (hx : x ∈ e.source) (v : TangentSpace (𝓡 3) x) :
      R.metric.tangentNorm (R.collapse x)
        (mfderiv (𝓡 3) (𝓡 3) R.collapse x v) = g.tangentNorm x v :=
    congrArg Real.sqrt (R.retained_metric x (Or.inl hx) v v)
  have hf := e.contMDiffOn.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hi := e.contMDiffOn_invFun.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hupper := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
    g R.metric e.toOpenPartialHomeomorph hf (C := 1) zero_lt_one
    (fun x hx v => by
      change R.metric.tangentNorm (R.collapse x)
        (mfderiv (𝓡 3) (𝓡 3) R.collapse x v) ≤ 1 * g.tangentNorm x v
      simpa only [one_mul] using (hnorm x hx v).le) hA hAU
  have hlower := M34.calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower
    g R.metric e.toOpenPartialHomeomorph hf hi (C := 1) zero_lt_one
    (fun x hx v => by
      change g.tangentNorm x v ≤ 1 * R.metric.tangentNorm (R.collapse x)
        (mfderiv (𝓡 3) (𝓡 3) R.collapse x v)
      simpa only [one_mul] using (hnorm x hx v).ge) hA hAU
  exact le_antisymm
    (by simpa only [hmap, ENNReal.ofReal_one, one_pow, one_mul] using hupper)
    (by simpa only [hmap, ENNReal.ofReal_one, one_pow, one_mul] using hlower)

end PoincareConjecture.Proofs.M47
