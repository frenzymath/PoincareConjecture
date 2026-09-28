import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SourceBranches

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SeparatedCircleSource.exists_original_source_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    {i : D.decomposition.Index} {L d : ℝ}
    (T : ComponentIdentityAnnuliData (e := e) (R := R) D.decomposition i L d)
    (hi : D.decomposition.pieces i = C₀)
    (hmi : D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁)
    (j : Fin 2) :
    ∃ (A : Set P2) (c : squareAnnulus L d ≃ₜ A), c.IsFinitePL ∧
      A ⊆ (if T.label j = 0 then interior S₀ else interior S₁) ∧
      (∀ p, (if T.label j = 0 then f₀ else f₁) (c p) = D.map (T.chart j p)) ∧
      (fun p : squareAnnulus L d => (c p : P2)) '' {p | depth L p = 0} =
        (if T.label j = 0 then C₀ else C₁) := by
  have hsub := D.identity_source_subset T hi hmi j
  have hmid := T.middle_image j
  rw [hi,hmi] at hmid
  by_cases hj : T.label j = 0
  · simp only [hj,if_true] at hsub hmid ⊢
    exact ⟨T.source j,T.chart j,T.chart_PL j,hsub.trans D.first_subset,
      fun p => (D.first_value (hsub (T.chart j p).property)).symm,hmid⟩
  · simp only [hj,if_false] at hsub hmid ⊢
    let A := D.shift.symm '' T.source j
    let c : squareAnnulus L d ≃ₜ A :=
      (T.chart j).trans (D.shift.symm.toHomeomorph.image (T.source j))
    have hc : c.IsFinitePL := by
      obtain ⟨u,hu,huv⟩ := T.chart_PL j
      refine ⟨D.shift.symm ∘ u,hu.postcomp D.shift.symm.toContinuousAffineMap,?_⟩
      intro p
      exact congrArg D.shift.symm (huv p)
    have hval (p : squareAnnulus L d) : f₁ (c p) = D.map (T.chart j p) := by
      obtain ⟨x,hx,hxp⟩ := hsub (T.chart j p).property
      change f₁ (D.shift.symm (T.chart j p)) = _
      rw [← hxp,D.shift.symm_apply_apply]
      exact (D.second_value x hx).symm
    refine ⟨A,c,hc,?_,hval,?_⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,rfl⟩ := hsub hx
      simpa only [D.shift.symm_apply_apply] using D.second_subset hy
    · change (D.shift.symm ∘ (fun p : squareAnnulus L d => (T.chart j p : P2))) ''
        {p | depth L p = 0} = C₁
      rw [image_comp,hmid]
      ext x
      constructor
      · rintro ⟨_,⟨y,hy,rfl⟩,h⟩
        rw [D.shift.symm_apply_apply] at h
        exact h ▸ hy
      · intro hx
        exact ⟨D.shift x,⟨x,hx,rfl⟩,D.shift.symm_apply_apply x⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
