import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointMaps
import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallBoundary

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem finitePL_ball_boundary_iff
    {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s b : Set E} {t c : Set F}
    (hs : IsFinitePLBallPair V s b) (ht : IsFinitePLBallPair V t c)
    (e : s ≃ₜ t) (he : e.IsFinitePL) (x : s) :
    (x : E) ∈ b ↔ (e x : F) ∈ c := by
  obtain ⟨f, hf, hval⟩ := he
  have hinj : InjOn f s := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hval ⟨z, hz⟩).trans (hzw.trans (hval ⟨w, hw⟩).symm))))
  have himage : f '' s = t := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hval ⟨z, hz⟩]
      exact (e ⟨z, hz⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hval, e.apply_symm_apply]
  have hball := hs.image hf hinj
  rw [himage] at hball
  have hboundary : f '' b = c := hball.boundary_eq_of_same_carrier ht
  rw [← hboundary, hval]
  constructor
  · exact fun hx => mem_image_of_mem f hx
  · rintro ⟨z, hz, hzx⟩
    exact hinj (hs.1 hz) x.property hzx ▸ hz

theorem signed_quarter_outer_arc_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (eps delta : Bool) {Q outer radial ends : Set E}
    (hQ : IsFinitePLBallPair (ℝ × ℝ) Q (outer ∪ radial))
    (hinter : outer ∩ radial = ends)
    (e : signedTubeQuarter eps delta ≃ₜ Q) (he : e.IsFinitePL)
    (hradial : ∀ x : signedTubeQuarter eps delta,
      (x : ℝ × ℝ) ∈ signedTubeRadialRim eps delta ↔ (e x : E) ∈ radial)
    (hends : ∀ x : signedTubeQuarter eps delta, (x : ℝ × ℝ) ∈
      ({signedTubeCorner 0 delta, signedTubeCorner 1 eps} : Set (ℝ × ℝ)) ↔ (e x : E) ∈ ends)
    (x : signedTubeQuarter eps delta) :
    (x : ℝ × ℝ) ∈ signedTubeOuterArc eps delta ↔ (e x : E) ∈ outer := by
  have hboundary := finitePL_ball_boundary_iff (signedTube_quarter_ball eps delta) hQ e he x
  have hs := Set.ext_iff.mp (signedTube_outer_inter_rim eps delta) (x : ℝ × ℝ)
  have ht := Set.ext_iff.mp hinter (e x : E)
  have hr := hradial x
  have hm := hends x
  change ((x : ℝ × ℝ) ∈ signedTubeOuterArc eps delta ∨
      (x : ℝ × ℝ) ∈ signedTubeRadialRim eps delta) ↔
    ((e x : E) ∈ outer ∨ (e x : E) ∈ radial) at hboundary
  change ((x : ℝ × ℝ) ∈ signedTubeOuterArc eps delta ∧
      (x : ℝ × ℝ) ∈ signedTubeRadialRim eps delta) ↔
    (x : ℝ × ℝ) ∈ ({signedTubeCorner 0 delta, signedTubeCorner 1 eps} : Set (ℝ × ℝ)) at hs
  change ((e x : E) ∈ outer ∧ (e x : E) ∈ radial) ↔ (e x : E) ∈ ends at ht
  tauto

end PoincareConjecture.M76.Dehn
