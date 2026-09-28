import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RetractionHessianIdentity
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Mathlib.RetractionParabolicPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

noncomputable def ambientCurvePrincipal (F : RicciFlow n M (Icc a b))
    (ρ : W → M) (t : ℝ) (z v : W) : ℝ :=
  ((F.metric t).inner (ρ z) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v))⁻¹

noncomputable def ambientCurveLower (F : RicciFlow n M (Icc a b))
    (e : M → W) (ρ : W → M) (t : ℝ) (z v : W) : W :=
  -(ambientCurvePrincipal F ρ t z v • coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v))

theorem ambientCurveCoefficients_contDiffOn (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) :
    let S : Set ((ℝ × W) × W) := {z | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0}
    ContDiffOn ℝ ∞ (fun z : (ℝ × W) × W =>
      ambientCurvePrincipal F ρ z.1.1 z.1.2 z.2) S ∧
    ContDiffOn ℝ ∞ (fun z : (ℝ × W) × W =>
      ambientCurveLower F e ρ z.1.1 z.1.2 z.2) S ∧
    ∀ t z, z ∈ U → ∀ v : W, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v ≠ 0 →
      0 < ambientCurvePrincipal F ρ t z v := by
  let S : Set ((ℝ × W) × W) := {z | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
    mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0}
  have hsub : S ⊆ (Icc a b ×ˢ U) ×ˢ univ := fun _ hz => ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (f := fun _ => 0) contMDiff_const).1.mono hsub
  have hA : ContDiffOn ℝ ∞ (fun z : (ℝ × W) × W =>
      ambientCurvePrincipal F ρ z.1.1 z.1.2 z.2) S :=
    hmetric.inv (fun z hz => ne_of_gt ((F.metric z.1.1).pos (ρ z.1.2) _ hz.2.2))
  refine ⟨hA, ?_, ?_⟩
  · exact (hA.smul ((flow_coordinateHessian_pullback_contDiffOn F he hU hρ).mono hsub)).neg
  · intro t z _ v hv
    exact inv_pos.mpr ((F.metric t).pos (ρ z) _ hv)

theorem ambientCurveCoefficients_retraction_defect (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (t : ℝ) {z : W} (hz : z ∈ U) (v : W) :
    retractionParabolicDefect (e ∘ ρ) (ambientCurvePrincipal F ρ)
      (ambientCurveLower F e ρ) t ((e ∘ ρ) z) (fderiv ℝ (e ∘ ρ) z v) = 0 := by
  let r : W → W := e ∘ ρ
  let p := ρ z
  let u := mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v
  let w := mfderiv (𝓡 n) 𝓘(ℝ, W) e p u
  let H := coordinateHessian (F.connection t) e p u u
  obtain ⟨hr, hDr, hleft⟩ := smooth_retraction_differentials he hU heU hρ hρe
  have hw : fderiv ℝ r z v = w := hDr z hz v
  have hH : coordinateHessian (F.connection t) e (ρ (e p))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) w)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e p) w) = H := by
    erw [hleft p u, hρe p]
  have hB : ambientCurveLower F e ρ t (e p) w =
      -(ambientCurvePrincipal F ρ t (e p) w • H) := by
    unfold ambientCurveLower
    rw [hH]
  have hnormal := coordinateHessian_retraction_identity (F.connection t) he hU heU
    (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun q => congrArg e (hρe q)) p u u
  change fderiv ℝ (fderiv ℝ r) (e p) w w + fderiv ℝ r (e p) H = H at hnormal
  change retractionParabolicDefect r (ambientCurvePrincipal F ρ)
    (ambientCurveLower F e ρ) t (e p) (fderiv ℝ r z v) = 0
  rw [hw, retractionParabolicDefect, hB,
    eq_sub_of_add_eq hnormal, map_neg, map_smul, smul_sub]
  abel

end PoincareConjecture.M63
