import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section





namespace Poincare.Manifold

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem exists_smooth_embedding_of_halfspace_charts
    (hn : Module.finrank ℝ E = n + 1) (K : Set M)
    (amb : K → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))))
    (hamb : ∀ a : K, (a : M) ∈ (amb a).source ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓡 (n + 1)) ∞ (amb a) (amb a).source ∧
      ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, E) ∞ (amb a).symm (amb a).target ∧
      (amb a).IsImage K {y | 0 ≤ y 0}) :
    ∃ (CS : ChartedSpace (EuclideanHalfSpace (n + 1)) K)
      (rel : K → OpenPartialHomeomorph K (EuclideanHalfSpace (n + 1)))
      (hsource : ∀ x : K, x ∈ (rel x).source),
      CS = chartedSpaceOfRelativeCharts rel hsource ∧
      @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
        (EuclideanHalfSpace (n + 1)) _ (𝓡∂ (n + 1)) ∞ K _ CS ∧
      Manifold.IsSmoothEmbedding (𝓡∂ (n + 1)) 𝓘(ℝ, E) ∞
        (fun x : K => (x : M)) := by
  let H := EuclideanHalfSpace (n + 1)
  let I := 𝓡∂ (n + 1)
  let rel : K → OpenPartialHomeomorph K H := fun a =>
    subtypeRestrictImageOn (amb a) (hamb a).2.2.2 a (hamb a).1
  have hsource (a : K) : a ∈ (rel a).source := by
    change a.1 ∈ (amb a).source
    exact (hamb a).1
  let CS : ChartedSpace H K := chartedSpaceOfRelativeCharts rel hsource
  have hman : @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      H _ I ∞ K _ CS := by
    letI : ChartedSpace H K := CS
    apply isManifold_of_contDiffOn I ∞ K
    rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
    let ea := amb a
    let eb := amb b
    let k := ea.symm.trans eb
    let r := I.symm ⁻¹' ((rel a).symm.trans (rel b)).source ∩ range I
    have hk : ContDiffOn ℝ ∞ k k.source := by
      apply (contMDiffOn_iff_contDiffOn).mp
      exact (hamb b).2.1.comp ((hamb a).2.2.1.mono (fun x hx => hx.1))
        (fun x hx => hx.2)
    apply contDiffOn_corner_transition_of_eqOn I k.open_source hk
      (fun x hx => by
        rcases hx.1 with h
        have hArel := h.1
        have hB := h.2
        have hxI : I (I.symm x) = x := I.right_inv hx.2
        have hAx' : ((I.symm x).val : EuclideanSpace ℝ (Fin (n + 1))) ∈ ea.target := by
          change ((I.symm x).val : EuclideanSpace ℝ (Fin (n + 1))) ∈ ea.target at hArel
          exact hArel
        have hAx : x ∈ ea.target := by
          rw [← hxI]
          exact hAx'
        have hco :
            (((rel a).symm (I.symm x) : K) : M) = ea.symm x := by
          have hc := subtypeRestrictImageOn_symm_apply_coe ea (hamb a).2.2.2 a
            (hamb a).1 hAx'
          have hIval : ((I.symm x).val : EuclideanSpace ℝ (Fin (n + 1))) = x := by
            exact I.right_inv hx.2
          change (((rel a).symm (I.symm x) : K) : M) = ea.symm ((I.symm x).val) at hc
          rw [hIval] at hc
          exact hc
        have hBx : ea.symm x ∈ eb.source := by
          change (((rel a).symm (I.symm x) : K) : M) ∈ eb.source at hB
          rw [hco] at hB
          exact hB
        exact ⟨hAx, hBx⟩)
    intro x hx
    have hxI : I (I.symm x) = x := I.right_inv hx.2
    have hArel := hx.1.1
    change ((I.symm x).val : EuclideanSpace ℝ (Fin (n + 1))) ∈ ea.target at hArel
    have hcoA :
        (((rel a).symm (I.symm x) : K) : M) = ea.symm x := by
      have hc := subtypeRestrictImageOn_symm_apply_coe ea (hamb a).2.2.2 a
        (hamb a).1 hArel
      have hIval : ((I.symm x).val : EuclideanSpace ℝ (Fin (n + 1))) = x := by
        exact I.right_inv hx.2
      change (((rel a).symm (I.symm x) : K) : M) = ea.symm ((I.symm x).val) at hc
      rw [hIval] at hc
      exact hc
    have hBrel := hx.1.2
    change ((rel b) ((rel a).symm (I.symm x)) : H).val = k x
    have hBsource : (rel a).symm (I.symm x) ∈ (rel b).source := hBrel
    have hcoB :
        (((rel b) ((rel a).symm (I.symm x)) : H).val :
          EuclideanSpace ℝ (Fin (n + 1))) =
          eb (((rel a).symm (I.symm x) : K) : M) := by
      exact subtypeRestrictImageOn_apply_coe (amb b) (hamb b).2.2.2 b
        (hamb b).1 hBsource
    rw [hcoB, hcoA]
    rfl
  refine ⟨CS, rel, hsource, rfl, hman, ?_⟩
  letI : ChartedSpace H K := CS
  letI : @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      H _ I ∞ K _ CS := hman
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨PUnit, by infer_instance, by infer_instance, ?_⟩
  intro a
  have ha : a ∈ (rel a).source := hsource a
  let B : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
  let cod : OpenPartialHomeomorph M E :=
    (amb a).trans B.toHomeomorph.toOpenPartialHomeomorph
  have hcod : cod ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
    apply cod.mem_maximalAtlas_of_contMDiffOn
    · simpa [cod, OpenPartialHomeomorph.trans_source, Function.comp_def] using
        ((ContinuousLinearEquiv.contDiff B).contMDiff.contMDiffOn.comp
          (hamb a).2.1 (fun x hx => (amb a).map_source hx))
    · simpa [cod, OpenPartialHomeomorph.trans_target, Function.comp_def] using
        ((hamb a).2.2.1.comp
          (ContinuousLinearEquiv.contDiff B.symm).contMDiff.contMDiffOn
          (by
            intro x hx
            change B.symm x ∈ (amb a).target at hx
            exact hx))
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (x := a) (f := fun x : K => (x : M))
    ((ContinuousLinearEquiv.prodUnique ℝ
      (EuclideanSpace ℝ (Fin (n + 1))) PUnit).trans B)
    (rel a) cod ?_ ?_ ?_ ?_ ?_ ?_
  · exact ha
  · simpa [cod, OpenPartialHomeomorph.trans_source] using (hamb a).1
  · change rel a ∈ IsManifold.maximalAtlas I ∞ K
    exact IsManifold.subset_maximalAtlas (chart_mem_atlas H a)
  · exact hcod
  · intro x hx
    change (x : M) ∈ (amb a).source at hx
    simpa [cod, OpenPartialHomeomorph.trans_source] using hx
  · intro x hx
    let y : K := ((rel a).extend I).symm x
    change (cod.extend 𝓘(ℝ, E)) (y : M) =
      ((ContinuousLinearEquiv.prodUnique ℝ
        (EuclideanSpace ℝ (Fin (n + 1))) PUnit).trans B) (x, 0)
    have hy : y ∈ (rel a).source := by
      simpa [y, OpenPartialHomeomorph.extend_source] using
        ((rel a).extend I).map_target hx
    have hrel := subtypeRestrictImageOn_apply_coe (amb a) (hamb a).2.2.2 a
      (hamb a).1 hy
    have hI : I (rel a (y : K)) = x := by
      have hright := (rel a).extend I |>.right_inv hx
      simpa [y, OpenPartialHomeomorph.extend_coe] using hright
    calc
      (cod.extend 𝓘(ℝ, E)) (y : M) = B (amb a (y : M)) := by
        simp [cod, Function.comp_apply]
      _ = B (I (rel a y)) := by
        congr 1
        exact hrel.symm
      _ = B x := by rw [hI]
      _ = ((ContinuousLinearEquiv.prodUnique ℝ
        (EuclideanSpace ℝ (Fin (n + 1))) PUnit).trans B) (x, 0) := by
        rfl

end Poincare.Manifold
