import PoincareConjecture.Definitions.Ch01.Topology



set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

structure PositiveThreeAtlas (M : Type u) [TopologicalSpace M] where
  charts : ChartedSpace (EuclideanSpace Real (Fin 3)) M
  positive_transition :
    ∀ (e e' : OpenPartialHomeomorph M (EuclideanSpace Real (Fin 3))),
      e ∈ charts.atlas → e' ∈ charts.atlas →
      ∀ (p : M), p ∈ e.source ∩ e'.source →
        0 < (fderiv Real (fun z => e' (e.symm z)) (e p)).toLinearMap.det

noncomputable def positiveThreeAtlasOfSigned
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (A : PoincareConjecture.OrientationCompatibleAtlas M) : PositiveThreeAtlas M := by
  classical
  let E := EuclideanSpace Real (Fin 3)
  let I := {e : OpenPartialHomeomorph M E // e ∈ atlas E M}
  let sector (e : I) (b : Bool) : Set M :=
    Subtype.val '' {p : e.1.source | A.chartSign e p = b}
  have sector_open (e : I) (b : Bool) : IsOpen (sector e b) :=
    e.1.open_source.isOpenMap_subtype_val _ ((A.chartSign_locallyConstant e).isOpen_fiber b)
  let R (b : Bool) : E ≃L[Real] E :=
    if b then ContinuousLinearEquiv.refl Real E else ContinuousLinearEquiv.neg Real
  have R_symm (b : Bool) : (R b).symm = R b := by cases b <;> rfl
  have R_invol (b : Bool) (x : E) : R b (R b x) = x := by
    simpa only [R_symm] using (R b).symm_apply_apply x
  have R_det (b : Bool) : (R b).toContinuousLinearMap.toLinearMap.det =
      (if b then (1 : Real) else -1) := by
    cases b
    · change (ContinuousLinearEquiv.neg Real : E ≃L[Real] E).toLinearEquiv.toLinearMap.det = -1
      have hn : (ContinuousLinearEquiv.neg Real : E ≃L[Real] E).toLinearEquiv.toLinearMap =
          (-1 : Real) • (LinearMap.id : E →ₗ[Real] E) := by
        ext x
        simp
      rw [hn, LinearMap.det_smul, LinearMap.det_id]
      norm_num [E, finrank_euclideanSpace]
    · change (LinearMap.id : E →ₗ[Real] E).det = 1
      exact LinearMap.det_id
  let corrected (e : I) (b : Bool) : OpenPartialHomeomorph M E :=
    (e.1.restrOpen (sector e b) (sector_open e b)).trans
      (R b).toHomeomorph.toOpenPartialHomeomorph
  have corrected_source (e : I) (b : Bool) :
      (corrected e b).source = e.1.source ∩ sector e b := by
    simp [corrected]
  have corrected_apply (e : I) (b : Bool) (p : M) : corrected e b p = R b (e.1 p) := rfl
  have corrected_symm (e : I) (b : Bool) (x : E) :
      (corrected e b).symm x = e.1.symm (R b x) := by
    change e.1.symm ((R b).symm x) = e.1.symm (R b x)
    rw [R_symm]
  have sign_eq (j : I) (a : Bool) (p : M) (h : p ∈ j.1.source) (hs : p ∈ sector j a) :
      A.chartSign j ⟨p, h⟩ = a := by
    rcases hs with ⟨⟨q, hq⟩, hsign, hqp⟩
    dsimp at hqp
    subst q
    exact hsign
  have positive (e e' : I) (b b' : Bool) (p : M)
      (hp : p ∈ (corrected e b).source ∩ (corrected e' b').source) :
      0 < (fderiv Real (fun z => corrected e' b' ((corrected e b).symm z))
        (corrected e b p)).toLinearMap.det := by
    rw [Set.mem_inter_iff, corrected_source, corrected_source] at hp
    obtain ⟨⟨hx, hs⟩, ⟨hx', hs'⟩⟩ := hp
    let F : E → E := fun z => e'.1 (e.1.symm z)
    have hpos := A.transition_positive e e' p hx hx'
    rw [sign_eq e b p hx hs, sign_eq e' b' p hx' hs', mfderiv_eq_fderiv] at hpos
    change 0 < (if b = b' then (1 : Real) else -1) *
      (fderiv Real F (e.1 p)).toLinearMap.det at hpos
    have hdiff : DifferentiableAt Real F (e.1 p) := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hpos
      simp at hpos
    have hf : HasFDerivAt F (fderiv Real F (e.1 p)) (R b (R b (e.1 p))) := by
      simpa only [R_invol] using hdiff.hasFDerivAt
    have hd := (R b').toContinuousLinearMap.hasFDerivAt.comp (R b (e.1 p))
      (hf.comp (R b (e.1 p)) (R b).toContinuousLinearMap.hasFDerivAt)
    have hderiv : fderiv Real (fun z => corrected e' b' ((corrected e b).symm z))
        (corrected e b p) =
        (R b').toContinuousLinearMap.comp
          ((fderiv Real F (e.1 p)).comp (R b).toContinuousLinearMap) := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
        corrected_apply, corrected_symm, F] using hd.fderiv
    rw [hderiv]
    change 0 < ((R b').toContinuousLinearMap.toLinearMap.comp
      ((fderiv Real F (e.1 p)).toLinearMap.comp
        (R b).toContinuousLinearMap.toLinearMap)).det
    rw [LinearMap.det_comp, LinearMap.det_comp, R_det, R_det]
    cases b <;> cases b' <;> simpa using hpos
  let chosen (p : M) : I := ⟨chartAt E p, chart_mem_atlas E p⟩
  let preferred (p : M) : I × Bool :=
    ⟨chosen p, A.chartSign (chosen p) ⟨p, mem_chart_source E p⟩⟩
  refine ⟨{
    atlas := Set.range (fun i : I × Bool => corrected i.1 i.2)
    chartAt := fun p => corrected (preferred p).1 (preferred p).2
    mem_chart_source := ?_
    chart_mem_atlas := fun p => ⟨preferred p, rfl⟩ }, ?_⟩
  · intro p
    rw [corrected_source]
    refine ⟨mem_chart_source E p, ?_⟩
    exact ⟨⟨p, mem_chart_source E p⟩, rfl, rfl⟩
  · intro c c' hc hc' p hp
    rcases hc with ⟨⟨e, b⟩, rfl⟩
    rcases hc' with ⟨⟨e', b'⟩, rfl⟩
    exact positive e e' b b' p hp

end PoincareConjecture.Proofs.M02.Topology
