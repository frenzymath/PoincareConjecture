import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderFlow
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndChartTransition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

theorem endCylinderAuxMetric_inverse (t : ℝ) {z : StandardCylinderSpace}
    (hz : 2 < z.2) (u v : StandardCapSpace) :
    (endCylinderAuxMetric e t).inner (e.coordinate z) u v =
      standardCylinderInner (endCylinderParameter t) z
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) v) := by
  have h := endCylinderAuxMetric_coordinate e t hz
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) v)
  rwa [end_coordinate_inverse_mfderiv e (by linarith),
    end_coordinate_inverse_mfderiv e (by linarith)] at h

theorem endCylinderAuxMetric_translation (t r : ℝ) {z : StandardCylinderSpace}
    (hz : 2 < z.2) (hrz : 2 < z.2 + r) (u v : StandardCapSpace) :
    (endCylinderAuxMetric e t).inner (e.coordinate z) u v =
      (endCylinderAuxMetric e t).inner (endAxialTranslation e r (e.coordinate z))
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (e.coordinate z) u)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (e.coordinate z) v) := by
  have hz0 : 0 < z.2 := by linarith
  have hrz0 : 0 < z.2 + r := by linarith
  change endCylinderCoefficients e (endCylinderParameter t) (e.coordinate z) u v =
    endCylinderCoefficients e (endCylinderParameter t) (endAxialTranslation e r (e.coordinate z))
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (e.coordinate z) u)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) (e.coordinate z) v)
  erw [endAxialTranslation_mfderiv e r hz0 hrz0,
    endAxialTranslation_mfderiv e r hz0 hrz0, endAxialTranslation_coordinate e r hz0.le]
  exact (endCylinderAuxMetric_inverse e t hz u v).trans
    (endCylinderAuxMetric_coordinate e t (z := (z.1, z.2 + r)) hrz
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) u)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.inverse (e.coordinate z) v)).symm

theorem endCylinderMetric_transition (p : endReferenceRegion e) (r : ℝ) (hr : -3 < r) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e), x ∈ endReferenceOverlap e r →
      ∀ u v : TangentSpace (𝓡 3) x,
        (endCylinderMetric e t).inner x u v =
          (endCylinderMetric e t).inner (endReferenceTransition e p r x)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x u)
            (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) x v) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t x hx u v
  rw [endCylinderMetric_inner, endCylinderMetric_inner,
    endReferenceTransition_mfderiv e p r hr x hx, endReferenceTransition_coe e p r hx]
  rcases x with ⟨x, hxU⟩
  obtain ⟨z, hz, rfl⟩ := hxU
  have hz3 : 3 < z.2 := hz.2.1
  have hz0 : 0 ≤ z.2 := by linarith
  have hrz0 : 0 ≤ z.2 + r := by linarith
  change endAxialTranslation e r (e.coordinate z) ∈ endReferenceRegion e at hx
  rw [endAxialTranslation_coordinate e r hz0] at hx
  obtain ⟨w, hw, hweq⟩ := hx
  have hw0 : 0 ≤ w.2 := by have h := hw.2.1; linarith
  have heq := congrArg e.inverse hweq
  rw [e.coordinate_left_inverse ⟨mem_univ _, hw0⟩,
    e.coordinate_left_inverse (show (z.1, z.2 + r) ∈ univ ×ˢ Ici (0 : ℝ) from
      ⟨mem_univ _, hrz0⟩)] at heq
  have hheight := congrArg Prod.snd heq
  have hrz : 2 < z.2 + r := by have h := hw.2.1; dsimp only at hheight; linarith
  exact endCylinderAuxMetric_translation e t r (by linarith) hrz u v

theorem endPullbackFlow_initial_eq_cylinder {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    (hinit : F.metric 0 = g) (s : ℝ) (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    (endPullbackFlow e F s hs).metric 0 = (endCylinderFlow e).metric 0 := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  apply Bundle.ContMDiffRiemannianMetric.eq_of_inner_eq
  intro x
  ext u v
  rw [endPullbackFlow_inner e F s hs]
  change (F.metric 0).inner (endAxialTranslation e s x)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x u)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x v) = (endCylinderMetric e 0).inner x u v
  rw [hinit, endCylinderMetric_inner, show endCylinderParameter 0 = 0 by
    simp [endCylinderParameter], endCylinderCoefficients_apply]
  simpa only [sub_zero, one_mul, zero_mul, add_zero] using
    (endReferenceTranslation_metric e hs x.property u v).symm

end PoincareConjecture.M34
