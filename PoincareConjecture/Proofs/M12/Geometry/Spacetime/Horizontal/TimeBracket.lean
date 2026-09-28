import PoincareConjecture.Definitions.M12HorizontalCalculus











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

namespace PoincareConjecture

private theorem bracket_annihilates_of_constant_derivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]
    {f : M → ℝ} (hf : ContMDiff J 𝓘(ℝ) ∞ f)
    (A B : (p : M) → TangentSpace J p) (a b : ℝ)
    (hA : ∀ p, mfderiv J 𝓘(ℝ) f p (A p) = a)
    (hB : ∀ p, mfderiv J 𝓘(ℝ) f p (B p) = b)
    (p : M)
    (hAd : MDifferentiableAt J (J.prod 𝓘(ℝ, E)) (T% A) p)
    (hBd : MDifferentiableAt J (J.prod 𝓘(ℝ, E)) (T% B) p) :
    mfderiv J 𝓘(ℝ) f p (VectorField.mlieBracket J A B p) = 0 := by
  have : IsManifold J (minSmoothness ℝ 2) M := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  let e := extChartAt J p
  let g : E → ℝ := f ∘ e.symm
  let V := VectorField.mpullbackWithin 𝓘(ℝ, E) J e.symm A (range J)
  let W := VectorField.mpullbackWithin 𝓘(ℝ, E) J e.symm B (range J)
  have hmem : e p ∈ e.target := mem_extChartAt_target p
  have hrange : e p ∈ range J := extChartAt_target_subset_range p hmem
  have hpe : e.symm (e p) = p := e.left_inv (mem_extChartAt_source p)
  have hg : ContDiffWithinAt ℝ ∞ g (range J) (e p) :=
    ((hf p).comp_contMDiffWithinAt_of_eq
      (contMDiffWithinAt_extChartAt_symm_range p hmem) hpe).contDiffWithinAt
  have hdiff (Z : (q : M) → TangentSpace J q)
      (hZ : MDifferentiableAt J (J.prod 𝓘(ℝ, E)) (T% Z) p) :
      DifferentiableWithinAt ℝ
        (VectorField.mpullbackWithin 𝓘(ℝ, E) J e.symm Z (range J)) (range J) (e p) := by
    simpa only [preimage_univ, univ_inter] using
      (hZ.mdifferentiableWithinAt (s := univ)).differentiableWithinAt_mpullbackWithin_vectorField
  have hchain (z : E) (hz : z ∈ e.target) :
      fderivWithin ℝ g (range J) z =
        (mfderiv J 𝓘(ℝ) f (e.symm z)).comp
          (mfderivWithin 𝓘(ℝ, E) J e.symm (range J) z) := by
    have hd := mfderiv_comp_mfderivWithin z
      ((hf (e.symm z)).mdifferentiableAt (by simp))
      (mdifferentiableWithinAt_extChartAt_symm hz)
      ((J.uniqueDiffOn z (extChartAt_target_subset_range p hz)).uniqueMDiffWithinAt)
    simpa only [mfderivWithin_eq_fderivWithin] using hd
  have hact (Z : (q : M) → TangentSpace J q) (c : ℝ)
      (hZ : ∀ q, mfderiv J 𝓘(ℝ) f q (Z q) = c) :
      (fun z ↦ fderivWithin ℝ g (range J) z
        (VectorField.mpullbackWithin 𝓘(ℝ, E) J e.symm Z (range J) z))
        =ᶠ[𝓝[range J] (e p)] (fun _ ↦ c) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := J) p] with z hz
    rw [hchain z hz]
    change mfderiv J 𝓘(ℝ) f (e.symm z)
      (mfderivWithin 𝓘(ℝ, E) J e.symm (range J) z
        ((mfderivWithin 𝓘(ℝ, E) J e.symm (range J) z).inverse (Z (e.symm z)))) = c
    rw [(isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse, hZ]
  have hcomm := VectorField.fderivWithin_apply_lieBracket hg
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    J.uniqueDiffOn
    (J.range_subset_closure_interior hrange) hrange (hdiff B hBd) (hdiff A hAd)
  have hzero : fderivWithin ℝ g (range J) (e p)
      (VectorField.lieBracketWithin ℝ V W (range J) (e p)) = 0 := by
    rw [hcomm, (hact B b hB).fderivWithin_eq_of_mem hrange,
      (hact A a hA).fderivWithin_eq_of_mem hrange]
    simp
  have hbase : fderivWithin ℝ g (range J) (e p) = mfderiv J 𝓘(ℝ) f p := by
    rw [hchain (e p) hmem]
    simp only [e, mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.comp_id]
    change (mfderiv J 𝓘(ℝ) f (e.symm (e p)) : E →L[ℝ] ℝ) = _
    rw [hpe]
  rw [hbase] at hzero
  change (mfderiv J 𝓘(ℝ) f p : E →L[ℝ] ℝ) _ = 0
  simpa only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    preimage_univ, univ_inter, mfderiv_extChartAt_self,
    ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply] using! hzero

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}

theorem IsSmoothHorizontalSectionOn.contMDiffOn_vectorField
    {V : HorizontalSection F} {U : Set F.Point} (hV : IsSmoothHorizontalSectionOn F V U) :
    ContMDiffOn (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (T% (horizontalSectionVectorField F V)) U := by
  have hinc : ContMDiff
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun v : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) F.Horizontal ↦
        Bundle.TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) v.proj v.2.val) :=
    F.horizontal_inclusion_smooth
  exact hinc.comp_contMDiffOn hV

theorem horizontalTimeBracket_is_horizontal
    {U : Set F.Point} (hU : IsOpen U) {V : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U) {p : F.Point} (hp : p ∈ U) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p
      (VectorField.mlieBracket (spacetimeModel n)
        (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
        (horizontalSectionVectorField F V) p) = 0 := by
  have hT : ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (T% (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)) :=
    F.timeVector_smooth
  apply bracket_annihilates_of_constant_derivatives (M := F.Point) F.time_smooth
    (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
    (horizontalSectionVectorField F V) 1 0 F.timeVector_normalized
    (fun q ↦ (V q).property) p
    ((hT p).mdifferentiableAt (by simp))
  exact (hV.contMDiffOn_vectorField.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)

theorem horizontalTimeBracket_val
    {U : Set F.Point} (hU : IsOpen U) {V : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U) {p : F.Point} (hp : p ∈ U) :
    (horizontalTimeBracket F V p).val =
      VectorField.mlieBracket (spacetimeModel n)
        (show (q : F.Point) → TangentSpace (spacetimeModel n) q from F.timeVector)
        (horizontalSectionVectorField F V) p := by
  exact congrArg Subtype.val (F.horizontalProjection_identity p
    ⟨_, horizontalTimeBracket_is_horizontal hU hV hp⟩)


theorem horizontalSectionBracket_is_horizontal
    {U : Set F.Point} (hU : IsOpen U) {V W : HorizontalSection F}
    (hV : IsSmoothHorizontalSectionOn F V U)
    (hW : IsSmoothHorizontalSectionOn F W U) {p : F.Point} (hp : p ∈ U) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p
      (VectorField.mlieBracket (spacetimeModel n)
        (horizontalSectionVectorField F V) (horizontalSectionVectorField F W) p) = 0 := by
  exact bracket_annihilates_of_constant_derivatives (M := F.Point) F.time_smooth
    (horizontalSectionVectorField F V) (horizontalSectionVectorField F W) 0 0
    (fun q => (V q).property) (fun q => (W q).property) p
    ((hV.contMDiffOn_vectorField.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hW.contMDiffOn_vectorField.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))

end PoincareConjecture
