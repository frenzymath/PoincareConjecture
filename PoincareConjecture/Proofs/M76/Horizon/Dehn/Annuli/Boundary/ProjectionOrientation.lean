import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.StandardFrontierOrientation

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

variable {X E ι κ : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem plAtlasTransitionSign_eq_one_of_common_coordinates
    (q : κ → OpenPartialHomeomorph X E)
    (hq : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid E)
    (i j : κ) (P : X → E)
    (hi : EqOn (q i) P (q i).source) (hj : EqOn (q j) P (q j).source)
    (x : ((q i).source ∩ (q j).source : Set X)) :
    plAtlasTransitionSign q hq i j x = 1 := by
  let H := (q i).symm.trans (q j)
  have hx : q i x ∈ H.source := by
    refine ⟨(q i).map_source x.property.1, ?_⟩
    change (q i).symm (q i x) ∈ (q j).source
    rw [(q i).left_inv x.property.1]
    exact x.property.2
  have heq : EqOn H (OpenPartialHomeomorph.refl E) H.source := by
    intro y hy
    change y ∈ (q i).target ∧ (q i).symm y ∈ (q j).source at hy
    change q j ((q i).symm y) = y
    rw [hj hy.2, ← hi ((q i).map_target hy.1), (q i).right_inv hy.1]
  exact (plLocalSign_eq_of_eqOn H (OpenPartialHomeomorph.refl E)
    (hq i j) (piecewiseAffineGroupoid E).id_mem hx (mem_univ _)
    H.open_source hx heq).trans (plLocalSign_refl ⟨q i x, mem_univ _⟩)

theorem exists_chart_labels_of_neutral_cover
    (q : κ → OpenPartialHomeomorph X E)
    (hq : ∀ i j, (q i).symm.trans (q j) ∈ piecewiseAffineGroupoid E)
    (base : ι → κ) (hcover : ∀ x : X, ∃ i, x ∈ (q (base i)).source)
    (hneutral : ∀ i j (x : ((q (base i)).source ∩ (q (base j)).source : Set X)),
      plAtlasTransitionSign q hq (base i) (base j) x = 1) :
    ∃ label : ∀ j, LocallyConstant (q j).source PLOrientationSheet,
      ∀ j k (x : X) (hj : x ∈ (q j).source) (hk : x ∈ (q k).source),
        (label k ⟨x, hk⟩).val =
          plAtlasTransitionSign q hq j k ⟨x, hj, hk⟩ * (label j ⟨x, hj⟩).val := by
  classical
  choose index hindex using hcover
  let f (j : κ) (x : (q j).source) : SignType :=
    plAtlasTransitionSign q hq (base (index x)) j ⟨x, hindex x, x.property⟩
  have hf (j : κ) (x : (q j).source) (i : ι) (hi : (x : X) ∈ (q (base i)).source) :
      f j x = plAtlasTransitionSign q hq (base i) j ⟨x, hi, x.property⟩ := by
    have h := plAtlasTransitionSign_cocycle q hq (base (index x)) (base i) j
      x (hindex x) hi x.property
    rw [hneutral, mul_one] at h
    exact h.symm
  have hc (j : κ) : Continuous (f j) := by
    rw [continuous_iff_continuousAt]
    intro x
    let i := index (x : X)
    let U : Set (q j).source := {z | (z : X) ∈ (q (base i)).source}
    have hU : IsOpen U := (q (base i)).open_source.preimage continuous_subtype_val
    have hxU : x ∈ U := hindex x
    let r : U → ((q (base i)).source ∩ (q j).source : Set X) :=
      fun z ↦ ⟨z.val, z.property, z.val.property⟩
    have hr : Continuous r :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hlocal : Continuous (fun z : U ↦ f j z.val) := by
      have heq : (fun z : U ↦ f j z.val) =
          plAtlasTransitionSign q hq (base i) j ∘ r := by
        funext z
        exact hf j z.val i z.property
      rw [heq]
      exact (isLocallyConstant_plAtlasTransitionSign q hq (base i) j).continuous.comp hr
    exact (continuousOn_iff_continuous_domRestrict.mpr hlocal).continuousAt (hU.mem_nhds hxU)
  let label (j : κ) : LocallyConstant (q j).source PLOrientationSheet :=
    ⟨fun x ↦ ⟨f j x, plAtlasTransitionSign_ne_zero q hq _ _ _⟩,
      (IsLocallyConstant.iff_continuous _).mpr ((hc j).subtype_mk _)⟩
  refine ⟨label, ?_⟩
  intro j k x hj hk
  exact (plAtlasTransitionSign_cocycle q hq (base (index x)) j k
    x (hindex x) hj hk).symm

end PoincareConjecture.M76.Dehn
