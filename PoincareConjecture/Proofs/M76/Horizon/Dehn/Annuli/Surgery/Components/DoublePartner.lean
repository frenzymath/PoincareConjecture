import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.LocalInjectivity
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteDoubleRelation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_finite_source_double_partner
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space)
    (hclosed : IsClosed (doubleLocusOn f K.space))
    (hcross : ∀ x ∈ K.space, ∀ y ∈ K.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f K.space R x y))
    (hunique : ∀ x ∈ K.space, ∀ y ∈ K.space, ∀ z ∈ K.space,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z) :
    ∃ (G : SimplicialComplex ℝ E) (partner : G.space ≃ₜ G.space),
      G.faces.Finite ∧ G.space = doubleLocusOn f K.space ∧
      partner.IsFinitePL ∧ partner.symm.IsFinitePL ∧ Function.Involutive partner ∧
      (∀ x : G.space, (partner x : E) ≠ x) ∧
      (∀ x : G.space, f (partner x) = f x) ∧
      ∀ (x : G.space) (y : E), y ∈ K.space → (x : E) ≠ y →
        f x = f y → y = (partner x : E) := by
  obtain ⟨L, hL, hLs⟩ := hf.exists_finite_double_relation_complex he K hK
    (isLocallyInjective_of_raw_source_crossings hclosed hcross)
  have hfirst : InjOn Prod.fst L.space := by
    intro z hz w hw heq
    rw [hLs] at hz hw
    apply Prod.ext heq
    exact hunique z.1 hz.1 z.2 hz.2.1 w.2 hw.2.1 hz.2.2.2
      (heq.symm ▸ hw.2.2.2) hz.2.2.1 ((congrArg f heq).trans hw.2.2.1)
  let first : E × E →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E E).toContinuousAffineMap
  have hfaces := L.affineOnFaces_affine first
  let G := hfaces.embeddedImage hfirst
  have hG : G.faces.Finite := hfaces.embeddedImage_finite hfirst hL
  have hGs : G.space = Prod.fst '' L.space := hfaces.embeddedImage_space hfirst
  obtain ⟨H₀, hH₀, hH₀val⟩ := (hfaces.finitePiecewiseAffineOn hL).exists_homeomorph_image hfirst
  let H : L.space ≃ₜ G.space := H₀.trans (Homeomorph.setCongr hGs.symm)
  have hH : H.IsFinitePL := hH₀.trans (Homeomorph.isFinitePL_setCongr hGs.symm G hG hGs)
  have hHval (z : L.space) : (H z : E) = z.val.1 := hH₀val z
  have hGdouble : G.space = doubleLocusOn f K.space := by
    rw [hGs, hLs]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz.1, z.2, hz.2.1, hz.2.2.1, hz.2.2.2⟩
    · rintro ⟨hx, y, hy, heq, hne⟩
      exact ⟨(x, y), ⟨hx, hy, heq, hne⟩, rfl⟩
  have hswap (z : L.space) : z.val.swap ∈ L.space := by
    have hz := hLs.subset z.property
    exact hLs.symm.subset ⟨hz.2.1, hz.1, hz.2.2.1.symm, hz.2.2.2.symm⟩
  let swap : L.space ≃ₜ L.space := {
    toFun := fun z ↦ ⟨z.val.swap, hswap z⟩
    invFun := fun z ↦ ⟨z.val.swap, hswap z⟩
    left_inv := fun z ↦ Subtype.ext (Prod.swap_swap z.val)
    right_inv := fun z ↦ Subtype.ext (Prod.swap_swap z.val)
    continuous_toFun :=
      (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _ }
  have hswapPL : swap.IsFinitePL :=
    ⟨Prod.swap, ⟨L, hL, rfl, L.affineOnFaces_affine
      (ContinuousLinearEquiv.prodComm ℝ E E).toContinuousLinearMap.toContinuousAffineMap⟩,
      fun _ ↦ rfl⟩
  let partner := H.symm.trans (swap.trans H)
  have hp : partner.IsFinitePL := hH.symm.trans (hswapPL.trans hH)
  have hback (x : G.space) : (H.symm x).val.1 = (x : E) := by
    rw [← hHval, H.apply_symm_apply]
  have hvalue (x : G.space) : (partner x : E) = (H.symm x).val.2 :=
    hHval (swap (H.symm x))
  refine ⟨G, partner, hG, hGdouble, hp, hp.symm, ?_, ?_, ?_, ?_⟩
  · intro x
    apply H.symm.injective
    change H.symm (H (swap (H.symm (H (swap (H.symm x)))))) = H.symm x
    simp only [H.symm_apply_apply]
    exact Subtype.ext (Prod.swap_swap (H.symm x).val)
  · intro x hx
    have hz := hLs.subset (H.symm x).property
    exact hz.2.2.2 ((hback x).trans (hx.symm.trans (hvalue x)))
  · intro x
    have hz := (hLs.subset (H.symm x).property).2.2.1
    rw [hback, ← hvalue] at hz
    exact hz.symm
  · intro x y hy hne heq
    have hz := hLs.subset (H.symm x).property
    simp only [mem_ofPred_eq] at hz
    rw [hback, ← hvalue] at hz
    exact hunique x hz.1 y hy (partner x) hz.2.1 hne hz.2.2.2 heq hz.2.2.1

end PoincareConjecture.M76.Dehn.Annuli
