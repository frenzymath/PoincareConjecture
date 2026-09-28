import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.TangentialCharts
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasTransitionSigns

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)

variable {X ι : Type*} [TopologicalSpace X] {S : Set X} [Nonempty S]

omit [Nonempty S] in
private theorem inverse_mem_surface (A : BrownCollar.FlatteningAtlas P2 S ι)
    (i : ι) (z : P2) (hz : (z, (0 : ℝ)) ∈ (A.chart i).target) :
    (A.chart i).symm (z, 0) ∈ S := by
  apply (A.pair i _ ((A.chart i).map_target hz)).mpr
  rw [(A.chart i).right_inv hz]

noncomputable def atlasTangentialChart (A : BrownCollar.FlatteningAtlas P2 S ι)
    (i : ι) : OpenPartialHomeomorph S P2 := by
  classical
  let inv : P2 → S := fun z =>
    if hz : (z, (0 : ℝ)) ∈ (A.chart i).target then
      ⟨(A.chart i).symm (z, 0), inverse_mem_surface A i z hz⟩
    else Classical.choice inferInstance
  have hinv (z : P2) (hz : (z, (0 : ℝ)) ∈ (A.chart i).target) :
      (inv z : X) = (A.chart i).symm (z, 0) := by simp [inv, hz]
  refine {
    toFun := A.coordinate i
    invFun := inv
    source := A.baseSet i
    target := (fun z : P2 => (z, (0 : ℝ))) ⁻¹' (A.chart i).target
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := A.isOpen_baseSet i
    open_target := (A.chart i).open_target.preimage (continuous_id.prodMk continuous_const)
    continuousOn_toFun := ?_
    continuousOn_invFun := ?_ }
  · intro x hx
    change (A.coordinate i x, (0 : ℝ)) ∈ (A.chart i).target
    rw [A.base_coordinate i x hx]
    exact (A.chart i).map_source hx
  · intro z hz
    change (inv z : X) ∈ (A.chart i).source
    rw [hinv z hz]
    exact (A.chart i).map_target hz
  · intro x hx
    apply Subtype.ext
    rw [hinv _ (by
      rw [A.base_coordinate i x hx]
      exact (A.chart i).map_source hx), A.base_coordinate i x hx]
    exact (A.chart i).left_inv hx
  · intro z hz
    change (A.chart i (inv z : X)).1 = z
    rw [hinv z hz, (A.chart i).right_inv hz]
  · exact ((A.chart i).continuousOn.comp continuous_subtype_val.continuousOn
      (fun x hx => hx)).fst
  · rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.subtype_mk
    change Continuous (fun z : {z : P2 | (z, (0 : ℝ)) ∈ (A.chart i).target} =>
      (inv z : X))
    have he : (fun z : {z : P2 | (z, (0 : ℝ)) ∈ (A.chart i).target} =>
        (inv z : X)) = fun z => (A.chart i).symm (z.val, 0) := by
      funext z
      exact hinv z z.property
    rw [he]
    exact (A.chart i).symm.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun z => z.property)

theorem atlasTangentialChart_source (A : BrownCollar.FlatteningAtlas P2 S ι) (i : ι) :
    (atlasTangentialChart A i).source = A.baseSet i := rfl

theorem atlasTangentialChart_target (A : BrownCollar.FlatteningAtlas P2 S ι) (i : ι) :
    (atlasTangentialChart A i).target =
      (fun z : P2 => (z, (0 : ℝ))) ⁻¹' (A.chart i).target := rfl

theorem atlasTangentialChart_apply (A : BrownCollar.FlatteningAtlas P2 S ι)
    (i : ι) (x : S) : atlasTangentialChart A i x = A.coordinate i x := rfl

theorem atlasTangentialChart_inverse (A : BrownCollar.FlatteningAtlas P2 S ι)
    (i : ι) (z : P2) (hz : z ∈ (atlasTangentialChart A i).target) :
    ((atlasTangentialChart A i).symm z : X) = (A.chart i).symm (z, 0) := by
  classical
  change (↑(if hz' : (z, (0 : ℝ)) ∈ (A.chart i).target then
    (⟨(A.chart i).symm (z, 0), inverse_mem_surface A i z hz'⟩ : S)
    else Classical.choice (inferInstance : Nonempty S)) : X) = _
  rw [dif_pos (show (z, (0 : ℝ)) ∈ (A.chart i).target from hz)]

theorem atlasTangentialChart_transition_eqOnSource
    (A : BrownCollar.FlatteningAtlas P2 S ι) (i j : ι) :
    (atlasTangentialChart A i).symm.trans (atlasTangentialChart A j) ≈
      atlasTangentialTransition A i j := by
  have hsource : ((atlasTangentialChart A i).symm.trans
      (atlasTangentialChart A j)).source = (atlasTangentialTransition A i j).source := by
    ext z
    constructor
    · intro hz
      change (z, (0 : ℝ)) ∈ (A.chart i).target ∧
        (A.chart i).symm (z, 0) ∈ (A.chart j).source
      refine ⟨hz.1, ?_⟩
      have hzj := hz.2
      change ((atlasTangentialChart A i).symm z : X) ∈ (A.chart j).source at hzj
      rwa [atlasTangentialChart_inverse A i z hz.1] at hzj
    · intro hz
      have hzt : z ∈ (atlasTangentialChart A i).target := hz.1
      refine ⟨hzt, ?_⟩
      change ((atlasTangentialChart A i).symm z : X) ∈ (A.chart j).source
      rw [atlasTangentialChart_inverse A i z hzt]
      exact hz.2
  refine ⟨hsource, ?_⟩
  intro z hz
  change (A.chart j ((atlasTangentialChart A i).symm z : X)).1 =
    (A.chart j ((A.chart i).symm (z, 0))).1
  rw [atlasTangentialChart_inverse A i z hz.1]

theorem atlasTangentialChart_compatible
    (A : BrownCollar.FlatteningAtlas P2 S ι) (i j : ι)
    (hPL : A.transition i j ∈ piecewiseAffineGroupoid (P2 × ℝ)) :
    (atlasTangentialChart A i).symm.trans (atlasTangentialChart A j) ∈
      piecewiseAffineGroupoid P2 :=
  (piecewiseAffineGroupoid P2).mem_of_eqOnSource
    (tangentialTransition_mem_piecewiseAffineGroupoid _ hPL _)
    (atlasTangentialChart_transition_eqOnSource A i j)

theorem atlasTangentialChart_cover (A : BrownCollar.FlatteningAtlas P2 S ι) (x : S) :
    x ∈ (atlasTangentialChart A (A.indexAt x)).source :=
  A.mem_source_at x

theorem atlasTangentialChart_transitionSign
    (A : BrownCollar.FlatteningAtlas P2 S ι)
    (hPL : ∀ i j, A.transition i j ∈ piecewiseAffineGroupoid (P2 × ℝ))
    (i j : ι) (x : S) (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    plAtlasTransitionSign (atlasTangentialChart A)
      (fun i j => atlasTangentialChart_compatible A i j (hPL i j)) i j ⟨x, hx⟩ =
      plLocalSign (atlasTangentialTransition A i j)
        (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
        ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩ := by
  let H := (atlasTangentialChart A i).symm.trans (atlasTangentialChart A j)
  have he := atlasTangentialChart_transition_eqOnSource A i j
  have hcoord : A.coordinate i x ∈ H.source := by
    refine ⟨(atlasTangentialChart A i).map_source hx.1, ?_⟩
    change (atlasTangentialChart A i).symm (atlasTangentialChart A i x) ∈
      (atlasTangentialChart A j).source
    rw [(atlasTangentialChart A i).left_inv hx.1]
    exact hx.2
  exact plLocalSign_eq_of_eqOn H (atlasTangentialTransition A i j)
    (atlasTangentialChart_compatible A i j (hPL i j))
    (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
    hcoord (A.transition_mem_source i j x hx) H.open_source hcoord he.eqOn

end PoincareConjecture.M76.Dehn.Annuli.RimBands
