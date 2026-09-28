import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages



set_option autoImplicit false
open Set Geometry

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_composed_chart_coordinates
    {E V W X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (B : OpenPartialHomeomorph X V)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V)
    (H : OpenPartialHomeomorph V W) (hH : LocallyPiecewiseAffineOn H H.source)
    (x : K.space) (hxB : g x ∈ B.source) (hxH : B (g x) ∈ H.source) :
    ∃ (N : SimplicialComplex ℝ E) (U : Set K.space),
      N.faces.Finite ∧ N.space ⊆ K.space ∧ IsOpen U ∧ x ∈ U ∧
      Subtype.val '' U ⊆ N.space ∧
      (∀ z ∈ N.space, g z ∈ B.source ∧ B (g z) ∈ H.source) ∧
      FinitePiecewiseAffineOn (H ∘ B ∘ g) N.space ∧
      ∃ J : N.space ≃ₜ (H ∘ B ∘ g) '' N.space,
        J.IsFinitePL ∧ J.symm.IsFinitePL ∧
        (∀ z : N.space, (J z : W) = H (B (g z))) ∧
        ∀ w : (H ∘ B ∘ g) '' N.space, H (B (g (J.symm w))) = (w : W) := by
  let O : Set K.space := (fun z => g z) ⁻¹' (B.source ∩ B ⁻¹' H.source)
  have hO : IsOpen O := (B.isOpen_inter_preimage H.open_source).preimage
    hg.continuousOn.domRestrict
  obtain ⟨N, U, hN, hNK, hU, hxU, hUN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxB, hxH⟩
  have hchart (z : E) (hz : z ∈ N.space) :
      g z ∈ B.source ∧ B (g z) ∈ H.source := hNO
    (show (⟨z, hNK hz⟩ : K.space) ∈ (Subtype.val : K.space → E) ⁻¹' N.space from hz)
  have hcoords := (hg.restrict_finite N hN hNK).finitePiecewiseAffineOn_compatible_chart_finite_source
    N hN B hB (fun z hz => (hchart z hz).1)
  have hfull : FinitePiecewiseAffineOn (H ∘ B ∘ g) N.space :=
    hH.comp_finitePiecewiseAffineOn hcoords (fun z hz => (hchart z hz).2)
  have hinj : InjOn (H ∘ B ∘ g) N.space := by
    intro u hu v hv heq
    exact hgi (hNK hu) (hNK hv) (B.injOn (hchart u hu).1 (hchart v hv).1
      (H.injOn (hchart u hu).2 (hchart v hv).2 heq))
  obtain ⟨J, hJ, hJval⟩ := hfull.exists_homeomorph_image hinj
  refine ⟨N, U, hN, hNK, hU, hxU, hUN, hchart, hfull, J, hJ, hJ.symm, hJval, ?_⟩
  intro w
  exact (hJval (J.symm w)).symm.trans (congrArg Subtype.val (J.apply_symm_apply w))

end Geometry
