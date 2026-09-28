import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Koszul










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

private theorem projection_time_zero (p : F.Point) :
    F.horizontalProjection p (F.timeVector p) = 0 := by
  apply Subtype.ext
  simp only [F.horizontalProjection_eq, F.timeVector_normalized, one_smul, sub_self]
  rfl

private theorem projection_bracket_decomposition
    (f g : F.Point → ℝ) (V W : HorizontalSection F) {p : F.Point}
    (hf : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) f p)
    (hg : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) g p)
    (hV : MDifferentiableAt (spacetimeModel n) (spacetimeModel n).tangent
      (T% (horizontalSectionVectorField F V)) p)
    (hW : MDifferentiableAt (spacetimeModel n) (spacetimeModel n).tangent
      (T% (horizontalSectionVectorField F W)) p) :
    F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
      (fun q : F.Point => f q • F.timeVector q + (V q).val)
      (fun q : F.Point => g q • F.timeVector q + (W q).val) p) =
      f p • horizontalTimeBracket F W p - g p • horizontalTimeBracket F V p +
        (show F.Horizontal p from F.horizontalProjection p (VectorField.mlieBracket
          (spacetimeModel n) (horizontalSectionVectorField F V)
            (horizontalSectionVectorField F W) p)) := by
  let χ : (q : F.Point) → TangentSpace (spacetimeModel n) q := F.timeVector
  have hχs : ContMDiff (spacetimeModel n) (spacetimeModel n).tangent ∞ (T% χ) :=
    F.timeVector_smooth
  have hχ : MDifferentiableAt (spacetimeModel n) (spacetimeModel n).tangent (T% χ) p :=
    (hχs p).mdifferentiableAt (by simp)
  have hswap : VectorField.mlieBracket (spacetimeModel n)
      (horizontalSectionVectorField F V) χ p =
        -VectorField.mlieBracket (spacetimeModel n) χ (horizontalSectionVectorField F V) p :=
    VectorField.mlieBracket_swap_apply
  change F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
    (f • χ + horizontalSectionVectorField F V)
    (g • χ + horizontalSectionVectorField F W) p) = _
  simp only [VectorField.mlieBracket_add_left (hf.smul_section hχ) hV,
    VectorField.mlieBracket_add_right (hg.smul_section hχ) hW,
    VectorField.mlieBracket_smul_left hf hχ,
    VectorField.mlieBracket_smul_right hg hχ, VectorField.mlieBracket_self,
    Pi.zero_apply, smul_zero, smul_neg, add_zero, hswap, map_add, map_smul, map_neg,
    show F.horizontalProjection p (χ p) = 0 from projection_time_zero p, zero_add,
    horizontalTimeBracket]
  dsimp only [χ]
  abel



theorem horizontal_torsion_decomposition
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {O : Set F.Point} (hO : IsOpen O) (f g : F.Point → ℝ)
    {V W : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O) {p : F.Point} (hp : p ∈ O)
    (hf : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) f p)
    (hg : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) g p) :
    rawHorizontalCovariantDerivative D W p (f p • F.timeVector p + (V p).val) -
        rawHorizontalCovariantDerivative D V p (g p • F.timeVector p + (W p).val) =
      F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
        (fun q : F.Point => f q • F.timeVector q + (V q).val)
        (fun q : F.Point => g q • F.timeVector q + (W q).val) p) := by
  rw [projection_bracket_decomposition f g V W hf hg
    ((hV.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hW.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))]
  simp only [map_add, map_smul, rawHorizontalCovariantDerivative_time,
    rawHorizontalCovariantDerivative_horizontal]
  rw [← rawLeafwiseCovariantDerivative_torsion hCoordinates D cover hO hV hW hp]
  abel



theorem spacetime_clock_contMDiffAt
    {V : (p : F.Point) → TangentSpace (spacetimeModel n) p} {p : F.Point}
    (hV : ContMDiffAt (spacetimeModel n) (spacetimeModel n).tangent ∞ (T% V) p) :
    ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
      (fun q => (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q (V q))) p := by
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ F.timeFunction := F.time_smooth
  have hd := ((ht p).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := F.timeFunction) hV (ht p)
  simpa using (contMDiffAt_totalSpace.mp hd).2




theorem horizontalCovariantDerivative_projection_torsion
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {O : Set F.Point} (hO : IsOpen O)
    {V W : (p : F.Point) → TangentSpace (spacetimeModel n) p}
    (hV : ContMDiffOn (spacetimeModel n) (spacetimeModel n).tangent ∞ (T% V) O)
    (hW : ContMDiffOn (spacetimeModel n) (spacetimeModel n).tangent ∞ (T% W) O)
    {p : F.Point} (hp : p ∈ O) :
    rawHorizontalCovariantDerivative D (fun q => F.horizontalProjection q (W q)) p (V p) -
        rawHorizontalCovariantDerivative D (fun q => F.horizontalProjection q (V q)) p (W p) =
      F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n) V W p) := by
  let f : F.Point → ℝ := fun q => mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q (V q)
  let g : F.Point → ℝ := fun q => mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q (W q)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) v.proj
          (F.horizontalProjection v.proj v.2)) := F.horizontalProjection_smooth
  have hVh : IsSmoothHorizontalSectionOn F (fun q => F.horizontalProjection q (V q)) O :=
    hproj.comp_contMDiffOn hV
  have hWh : IsSmoothHorizontalSectionOn F (fun q => F.horizontalProjection q (W q)) O :=
    hproj.comp_contMDiffOn hW
  have hf := (spacetime_clock_contMDiffAt (hV.contMDiffAt (hO.mem_nhds hp))).mdifferentiableAt
    (by simp)
  have hg := (spacetime_clock_contMDiffAt (hW.contMDiffAt (hO.mem_nhds hp))).mdifferentiableAt
    (by simp)
  have h := horizontal_torsion_decomposition hCoordinates D cover hO f g hVh hWh hp hf hg
  have hVeq : (fun q => f q • F.timeVector q + (F.horizontalProjection q (V q)).val) = V :=
    funext fun q => (F.tangent_decomposition q (V q)).symm
  have hWeq : (fun q => g q • F.timeVector q + (F.horizontalProjection q (W q)).val) = W :=
    funext fun q => (F.tangent_decomposition q (W q)).symm
  rw [hVeq, hWeq] at h
  rw [congrFun hVeq p, congrFun hWeq p] at h
  exact h

end PoincareConjecture.M14
