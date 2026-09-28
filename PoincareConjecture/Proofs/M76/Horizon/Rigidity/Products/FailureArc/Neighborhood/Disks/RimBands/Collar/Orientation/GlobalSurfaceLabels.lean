import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasTransitionSigns

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

theorem exists_plAtlas_labels_of_global_chart
    {Y E ι : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : ι → OpenPartialHomeomorph Y E)
    (hq : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid E)
    (b : OpenPartialHomeomorph Y E) (hb : b.source = univ)
    (hqb : ∀ i, (q i).symm.trans b ∈ piecewiseAffineGroupoid E) :
    ∃ label : ∀ i, LocallyConstant (q i).source {s : SignType // s ≠ 0},
      ∀ i j (x : Y) (hi : x ∈ (q i).source) (hj : x ∈ (q j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign q hq i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let atlas : Option ι → OpenPartialHomeomorph Y E := fun i =>
    match i with
    | none => b
    | some i => q i
  have hbb : b.symm.trans b ∈ piecewiseAffineGroupoid E := by
    apply (piecewiseAffineGroupoid E).mem_of_eqOnSource _ b.symm_trans_self
    exact ((closedUnderRestriction_iff_id_le (piecewiseAffineGroupoid E)).mp
      inferInstance) (idRestrGroupoid_mem b.open_target)
  have ha : ∀ i j, (atlas i).symm.trans (atlas j) ∈ piecewiseAffineGroupoid E := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hbb
      | some j =>
        simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid E).symm (hqb j)
    | some i =>
      cases j with
      | none => exact hqb i
      | some j => exact hq i j
  have hglobal (x : Y) : x ∈ b.source := hb.symm ▸ mem_univ x
  let inc (i : ι) : (q i).source → ((atlas (some i)).source ∩ (atlas none).source : Set Y) :=
    fun x => ⟨x, x.property, hglobal x⟩
  have hinc (i : ι) : Continuous (inc i) := continuous_subtype_val.subtype_mk _
  let value (i : ι) (x : (q i).source) : SignType :=
    plAtlasTransitionSign atlas ha (some i) none (inc i x)
  have hvalue (i : ι) : IsLocallyConstant (value i) :=
    (isLocallyConstant_plAtlasTransitionSign atlas ha (some i) none).comp_continuous (hinc i)
  have hnonzero (i : ι) (x : (q i).source) : value i x ≠ 0 :=
    plAtlasTransitionSign_ne_zero atlas ha (some i) none (inc i x)
  let label (i : ι) : LocallyConstant (q i).source {s : SignType // s ≠ 0} :=
    ⟨fun x => ⟨value i x, hnonzero i x⟩, by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro x
      exact ((hvalue i).eventually_eq x).mono fun _ h => Subtype.ext h⟩
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have hc := plAtlasTransitionSign_cocycle atlas ha (some i) (some j) none x
    hi hj (hglobal x)
  have hc' : value j ⟨x, hj⟩ * plAtlasTransitionSign q hq i j ⟨x, hi, hj⟩ =
      value i ⟨x, hi⟩ := hc
  change value j ⟨x, hj⟩ = plAtlasTransitionSign q hq i j ⟨x, hi, hj⟩ * value i ⟨x, hi⟩
  have hn := plAtlasTransitionSign_ne_zero q hq i j ⟨x, hi, hj⟩
  cases hs : plAtlasTransitionSign q hq i j ⟨x, hi, hj⟩ <;>
    cases hv : value j ⟨x, hj⟩ <;> cases hw : value i ⟨x, hi⟩ <;> simp_all

end PoincareConjecture.M76.Dehn.Annuli.RimBands
