import PoincareConjecture.Proofs.M14.Sec6_2_MarkedGaugeVariation









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}

private theorem family_fixed_of_square {p : M14BackwardPath G T a b x y}
    {R : M14SquareRootPath G p} (V : M14LVariationData G p R) {t : ℝ}
    (ht : t ∈ Icc a b) (hfix : ∀ u, V.squareFamily (Real.sqrt t) u = R.curve (Real.sqrt t)) :
    ∀ u ∈ V.parameterDomain, V.family t u = p.curve t := by
  have hs : Real.sqrt t ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩
  intro u hu
  have hsq := V.square_agrees _ hs u hu
  rw [Real.sq_sqrt (p.tau_nonneg.trans ht.1)] at hsq
  rw [← hsq, hfix u, R.agrees _ hs, Real.sq_sqrt (p.tau_nonneg.trans ht.1)]




theorem exists_meetingGauge_variations (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (p : M14BackwardPath G T a c x (q.curve c))
    (hc : c < b) (Rp : M14SquareRootPath G p) (Rq : M14SquareRootPath G q)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ z ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift z) = z)
    (hqU : Rq.curve (Real.sqrt c) ∈ U) (w : EuclideanSpace ℝ (Fin n)) :
    ∃ Vp : M14LVariationData G p Rp, ∃ Vq : M14LVariationData G q Rq,
      Vp.left_endpoint_fixed ∧ M14BothEndpointsFixed Vq ∧
      (∀ u ∈ Vp.parameterDomain ∩ Vq.parameterDomain, Vp.family c u = Vq.family c u) ∧
      (M14VariationField Vp (Real.sqrt c)).val = ((G.gaugeCover.metric j).spatialTangentEquiv
        (lift (Rq.curve (Real.sqrt c))).1 (lift (Rq.curve (Real.sqrt c))).2 w).val ∧
      (M14VariationField Vq (Real.sqrt c)).val = ((G.gaugeCover.metric j).spatialTangentEquiv
        (lift (Rq.curve (Real.sqrt c))).1 (lift (Rq.curve (Real.sqrt c))).2 w).val := by
  have hc0 : 0 ≤ c := p.tau_nonneg.trans p.tau_lt.le
  have hsac : Real.sqrt a < Real.sqrt c := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hscb : Real.sqrt c < Real.sqrt b := Real.sqrt_lt_sqrt hc0 hc
  have hsp : Real.sqrt c ∈ M14SqrtParameterInterval a c := ⟨hsac.le, le_rfl⟩
  have hsq : Real.sqrt c ∈ M14SqrtParameterInterval a b := ⟨hsac.le, hscb.le⟩
  have hpoint : Rp.curve (Real.sqrt c) = Rq.curve (Real.sqrt c) := by
    rw [Rp.agrees _ hsp, Rq.agrees _ hsq, Real.sq_sqrt hc0, p.curve_end]
  obtain ⟨Vp, hpfixed, hpmark, hpfield⟩ := exists_markedGauge_variation hM12 Rp j lift
    hU hlift hright hsp (hpoint.symm ▸ hqU) isOpen_Ioo ⟨hsac, hscb⟩ w
  obtain ⟨Vq, hqfixed, hqmark, hqfield⟩ := exists_markedGauge_variation hM12 Rq j lift
    hU hlift hright hsq hqU isOpen_Ioo ⟨hsac, hscb⟩ w
  have hpa : Real.sqrt a ∈ M14SqrtParameterInterval a c := ⟨le_rfl, hsac.le⟩
  have hqa : Real.sqrt a ∈ M14SqrtParameterInterval a b :=
    ⟨le_rfl, (hsac.trans hscb).le⟩
  have hqb : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨(hsac.trans hscb).le, le_rfl⟩
  refine ⟨Vp, Vq, ?_, ?_, ?_, ?_, hqfield⟩
  · apply Vp.left_endpoint_fixed_spec.mpr
    exact family_fixed_of_square Vp ⟨le_rfl, p.tau_lt.le⟩
      (hpfixed _ hpa (fun ht => (lt_irrefl _ ht.1)))
  · constructor
    · apply Vq.left_endpoint_fixed_spec.mpr
      exact family_fixed_of_square Vq ⟨le_rfl, q.tau_lt.le⟩
        (hqfixed _ hqa (fun ht => (lt_irrefl _ ht.1)))
    · apply Vq.right_endpoint_fixed_spec.mpr
      exact family_fixed_of_square Vq ⟨q.tau_lt.le, le_rfl⟩
        (hqfixed _ hqb (fun ht => (lt_irrefl _ ht.2)))
  · intro u hu
    have hp := Vp.square_agrees _ hsp u hu.1
    have hq := Vq.square_agrees _ hsq u hu.2
    rw [Real.sq_sqrt hc0] at hp hq
    rw [← hp, ← hq, hpmark, hqmark, hpoint]
  · exact hpfield.trans (congrArg (fun z : G.Point =>
      ((G.gaugeCover.metric j).spatialTangentEquiv (lift z).1 (lift z).2 w).val) hpoint)

end PoincareConjecture.M14
