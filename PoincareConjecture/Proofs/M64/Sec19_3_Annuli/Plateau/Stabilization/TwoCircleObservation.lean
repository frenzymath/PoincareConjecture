import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.OriginalCircleObservation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64



theorem planarCircleObservation_injective {circumference : ℝ}
    (C : M62.CircleGeometry circumference) :
    Function.Injective (@planarCircleObservation circumference) := by
  intro q q' h
  apply AddCircle.injective_toCircle C.positive.ne'
  apply Subtype.ext
  apply Complex.ext
  · simpa only [planarCircleObservation, Matrix.cons_val_zero] using
      congrArg (fun p : LoopPlane => p 0) h
  · simpa only [planarCircleObservation, Matrix.cons_val_one, Matrix.cons_val_zero] using
      congrArg (fun p : LoopPlane => p 1) h

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem auxiliaryCircle_observation_with_two_circles
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) :
    ∃ (m : ℕ) (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
      (R T : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane),
      ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := (n + 1) + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.1.2) ∧
      ∀ q, T (e q) = planarCircleObservation q.2 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  obtain ⟨m0, e0, R0, he0, hei0, hread0, hR0, -⟩ :=
    auxiliaryCircle_observation_with_original_current P Q
  obtain ⟨m1, e1, R1, he1, -, -, hR1, -⟩ := circleProduct_observation_with_current Q
  let A : EuclideanSpace ℝ (Fin (m0 + m1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin m0) × EuclideanSpace ℝ (Fin m1) :=
    EuclideanSpace.finAddEquivProd
  let e : Q.charts.Point → EuclideanSpace ℝ (Fin (m0 + m1)) :=
    fun q => A.symm (e0 q, e1 q)
  let L0 : EuclideanSpace ℝ (Fin (m0 + m1)) →L[ℝ] EuclideanSpace ℝ (Fin m0) :=
    (ContinuousLinearMap.fst ℝ _ _).comp A.toContinuousLinearMap
  let L1 : EuclideanSpace ℝ (Fin (m0 + m1)) →L[ℝ] EuclideanSpace ℝ (Fin m1) :=
    (ContinuousLinearMap.snd ℝ _ _).comp A.toContinuousLinearMap
  have hL0 (q : Q.charts.Point) : L0 (e q) = e0 q := by
    change (A (A.symm (e0 q, e1 q))).1 = e0 q
    rw [A.apply_symm_apply]
  have hL1 (q : Q.charts.Point) : L1 (e q) = e1 q := by
    change (A (A.symm (e0 q, e1 q))).2 = e1 q
    rw [A.apply_symm_apply]
  have he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 (m0 + m1)) ∞ e :=
    A.symm.toDiffeomorph.contMDiff.comp (he0.prodMk_space he1)
  have hei : Function.Injective e := by
    intro q q' h
    apply hei0.injective
    simpa only [hL0] using congrArg L0 h
  refine ⟨m0 + m1, e, R0.comp L0, R1.comp L1, he,
    he.continuous.isClosedEmbedding hei, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨b, hb, R, hR⟩ := hread0 q
    refine ⟨b, hb, R.comp L0, ?_⟩
    simpa only [ContinuousLinearMap.comp_apply, hL0] using hR
  · intro q
    simp only [ContinuousLinearMap.comp_apply, hL0, hR0]
  · intro q
    simp only [ContinuousLinearMap.comp_apply, hL1, hR1]

omit [T2Space M] [CompactSpace M] in


theorem auxiliaryCircle_exists_separating_reader {m : ℕ}
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (T : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hT : ∀ q, T (e q) = planarCircleObservation q.2)
    {q0 q1 : Q.circle.Point} (hne : q0 ≠ q1) :
    ∃ (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (v0 v1 : ℝ),
      v0 ≠ v1 ∧ (∀ p : P.charts.Point, L (e (p, q0)) = v0) ∧
      ∀ p : P.charts.Point, L (e (p, q1)) = v1 := by
  have hdiff : planarCircleObservation q0 ≠ planarCircleObservation q1 :=
    fun h => hne (planarCircleObservation_injective Q.circle h)
  obtain ⟨i, hi⟩ : ∃ i : Fin 2,
      planarCircleObservation q0 i ≠ planarCircleObservation q1 i := by
    by_contra h
    push Not at h
    exact hdiff (PiLp.ext h)
  refine ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).comp T,
    planarCircleObservation q0 i, planarCircleObservation q1 i, hi, ?_, ?_⟩
  · intro p
    simp only [ContinuousLinearMap.comp_apply, hT, EuclideanSpace.coe_proj]
  · intro p
    simp only [ContinuousLinearMap.comp_apply, hT, EuclideanSpace.coe_proj]

end PoincareConjecture.M64
