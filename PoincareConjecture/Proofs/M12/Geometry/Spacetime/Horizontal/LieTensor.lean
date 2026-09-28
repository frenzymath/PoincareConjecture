import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.TimeBracket
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Choice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}

local notation "H% " V => (fun q : F.Point ↦ TotalSpace.mk'
  (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) q (V q))

private theorem horizontalField_differentiable
    {V : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p) :
    MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      (T% (horizontalSectionVectorField F V)) p := by
  have hinc : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal ↦
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) v.proj v.2.val) :=
    F.horizontal_inclusion_smooth
  exact (hinc.mdifferentiable (by simp) _).comp p hV

private theorem horizontalPair_differentiable
    {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p) :
    MDifferentiableAt (spacetimeModel n) 𝓘(ℝ)
      (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p := by
  have hg := (F.horizontalMetric.contMDiff p).mdifferentiableAt (by simp)
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : F.Point ↦ ℝ) hV hW
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

theorem horizontalTimeBracket_add
    {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p) :
    horizontalTimeBracket F (V + W) p =
      horizontalTimeBracket F V p + horizontalTimeBracket F W p := by
  have hv := horizontalField_differentiable hV
  have hw := horizontalField_differentiable hW
  unfold horizontalTimeBracket
  change F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
    _ (horizontalSectionVectorField F V + horizontalSectionVectorField F W) p) = _
  rw [VectorField.mlieBracket_add_right hv hw, map_add]

theorem horizontalTimeBracket_smul
    {V : HorizontalSection F} {f : F.Point → ℝ} {p : F.Point}
    (hf : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) f p)
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p) :
    horizontalTimeBracket F (f • V) p =
      mvfderiv (spacetimeModel n) f p (F.timeVector p) • V p +
        f p • horizontalTimeBracket F V p := by
  have hv := horizontalField_differentiable hV
  unfold horizontalTimeBracket
  change F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
    _ (f • horizontalSectionVectorField F V) p) = _
  rw [VectorField.mlieBracket_smul_right hf hv, map_add, map_smul, map_smul]
  rw [show F.horizontalProjection p (horizontalSectionVectorField F V p) = V p from
    F.horizontalProjection_identity p (V p)]

private theorem horizontalLie_tensorial_left (p : F.Point)
    (W : HorizontalSection F)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p) :
    TensorialAt (spacetimeModel n) (EuclideanSpace ℝ (Fin n))
      (fun V ↦ horizontalMetricLieDerivativeOnFields F V W p) p where
  smul {f V} hf hV := by
    simp only [horizontalMetricLieDerivativeOnFields, Pi.smul_apply', map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      mvfderiv_fun_mul hf (horizontalPair_differentiable hV hW),
      horizontalTimeBracket_smul hf hV, map_add, ContinuousLinearMap.add_apply]
    ring
  add hV hV' := by
    simp only [horizontalMetricLieDerivativeOnFields, Pi.add_apply, map_add,
      ContinuousLinearMap.add_apply,
      mvfderiv_fun_add (horizontalPair_differentiable hV hW)
        (horizontalPair_differentiable hV' hW), horizontalTimeBracket_add hV hV']
    ring

private theorem horizontalLie_tensorial_right (p : F.Point)
    (V : HorizontalSection F)
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p) :
    TensorialAt (spacetimeModel n) (EuclideanSpace ℝ (Fin n))
      (fun W ↦ horizontalMetricLieDerivativeOnFields F V W p) p := by
  simpa only [horizontalMetricLieDerivativeOnFields_symmetric V] using
    horizontalLie_tensorial_left p V hV

private noncomputable def horizontalLieBilinear (p : F.Point) :
    F.Horizontal p →L[ℝ] F.Horizontal p →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun V W ↦ horizontalMetricLieDerivativeOnFields F V W p) p
    (horizontalLie_tensorial_left p) (horizontalLie_tensorial_right p)

private theorem horizontalLieBilinear_eq (p : F.Point) (v w : F.Horizontal p) :
    horizontalLieBilinear p v w = horizontalMetricLieDerivative F p v w :=
  TensorialAt.mkHom₂_apply_eq_extend _ _ v w

theorem horizontalMetricLieDerivative_on_differentiable_fields
    {V W : HorizontalSection F} {p : F.Point}
    (hV : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% V) p)
    (hW : MDifferentiableAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (H% W) p) :
    horizontalMetricLieDerivative F p (V p) (W p) =
      horizontalMetricLieDerivativeOnFields F V W p := by
  rw [← horizontalLieBilinear_eq]
  exact TensorialAt.mkHom₂_apply _ _ hV hW

theorem horizontalMetricLieDerivative_on_fields
    {U : Set F.Point} (hU : IsOpen U) {V W : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U) (hW : IsSmoothHorizontalSectionOn F W U)
    {p : F.Point} (hp : p ∈ U) :
    horizontalMetricLieDerivative F p (V p) (W p) =
      horizontalMetricLieDerivativeOnFields F V W p :=
  horizontalMetricLieDerivative_on_differentiable_fields
    ((hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hW.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))

private theorem horizontalPair_smooth
    {V W : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% W) p) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q ↦ F.horizontalMetric.inner q (V q) (W q)) p := by
  have h := (F.horizontalMetric.contMDiff p).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : F.Point ↦ ℝ) hV hW
  exact (contMDiffAt_totalSpace.mp h).2

theorem horizontalTimeBracket_smooth
    {V : HorizontalSection F} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (H% V) p) :
    ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (H% (horizontalTimeBracket F V)) p := by
  have hinc : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal ↦
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) v.proj v.2.val) :=
    F.horizontal_inclusion_smooth
  have hfield : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (T% (horizontalSectionVectorField F V)) p := (hinc _).comp p hV
  have hT : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (T% (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)) :=
    F.timeVector_smooth
  have : IsManifold (spacetimeModel n) (∞ + 1) F.Point := by
    simpa using (inferInstance : IsManifold (spacetimeModel n) ∞ F.Point)
  have : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) F.Point := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hbracket := (hT p).mlieBracket_vectorField hfield (m := ⊤) (by simp)
  have hproj : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) F.Point ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := F.Horizontal) v.proj (F.horizontalProjection v.proj v.2)) :=
    F.horizontalProjection_smooth
  exact (hproj _).comp p hbracket

theorem horizontalMetricLieDerivativeOnFields_smooth
    {U : Set F.Point} (hU : IsOpen U) {V W : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U) (hW : IsSmoothHorizontalSectionOn F W U) :
    ContMDiffOn (spacetimeModel n) 𝓘(ℝ) ∞
      (horizontalMetricLieDerivativeOnFields F V W) U := by
  intro p hp
  have hv := hV.contMDiffAt (hU.mem_nhds hp)
  have hw := hW.contMDiffAt (hU.mem_nhds hp)
  have hg := horizontalPair_smooth hv hw
  have hT : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (T% (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)) :=
    F.timeVector_smooth
  have hd := (hg.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates (hT p) hg
  have hderiv : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q ↦ mvfderiv (spacetimeModel n)
        (fun r ↦ F.horizontalMetric.inner r (V r) (W r)) q (F.timeVector q)) p := by
    rw [contMDiffAt_totalSpace] at hd
    simp only [id_eq] at hd
    convert hd.2 using 1
    funext q
    simp only [mvfderiv, ContinuousLinearMap.comp_apply]
    simp
    rfl
  exact ((hderiv.sub (horizontalPair_smooth (horizontalTimeBracket_smooth hv) hw)).sub
    (horizontalPair_smooth hv (horizontalTimeBracket_smooth hw))).contMDiffWithinAt

theorem horizontalMetricLieDerivative_tensor :
    IsSmoothHorizontalCovariantTensor F (k := 2)
      (fun p v ↦ horizontalMetricLieDerivative F p (v 0) (v 1)) := by
  classical
  constructor
  · intro p
    let B := horizontalLieBilinear (F := F) p
    refine ⟨MultilinearMap.mk' (fun v : Fin 2 → F.Horizontal p ↦ B (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i <;> simp [map_add])
      (by
        intro v i a x
        fin_cases i <;> simp [map_smul]), ?_⟩
    intro v
    exact (horizontalLieBilinear_eq p (v 0) (v 1)).symm
  · intro U hU V hV
    apply (horizontalMetricLieDerivativeOnFields_smooth hU (hV 0) (hV 1)).congr
    intro p hp
    exact horizontalMetricLieDerivative_on_fields hU (hV 0) (hV 1) hp

end PoincareConjecture
