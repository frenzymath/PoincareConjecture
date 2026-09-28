import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.exists_finite_branch_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {a b : E}
    (C : RawSourceCrossing e f S R a b) (hf : PolyhedralPLInCharts e f S)
    (side : Bool) (x : S) (hx : (x : E) ∈ if side then C.right else C.left) :
    ∃ (N : SimplicialComplex ℝ E) (V : Set S),
      N.faces.Finite ∧ N.space ⊆ (if side then C.right else C.left) ∧
      IsOpen V ∧ x ∈ V ∧ Subtype.val '' V ⊆ N.space ∧
      FinitePiecewiseAffineOn (C.chart ∘ f) N.space ∧
      ∃ H : N.space ≃ₜ (C.chart ∘ f) '' N.space,
        H.IsFinitePL ∧ H.symm.IsFinitePL ∧
        (∀ z : N.space, (H z : V3) = C.chart (f z)) ∧
        (∀ w : (C.chart ∘ f) '' N.space, C.chart (f (H.symm w)) = (w : V3)) := by
  let B := if side then C.right else C.left
  have hBo : IsOpen ((Subtype.val : S → E) ⁻¹' B) := by
    cases side <;> first | exact C.left_open | exact C.right_open
  have hBe : IsEmbedding (fun z : B ↦ f z) := by
    cases side <;> first | exact C.left_embedding | exact C.right_embedding
  have hBT (z : E) (hz : z ∈ B) : f z ∈ C.chart.source := by
    apply (C.whole_preimage.symm.subset ?_).2
    cases side
    · exact Or.inl hz
    · exact Or.inr hz
  obtain ⟨_, J, V0, hJ, hJD, hV0, hxV0, hV0J, _, _⟩ := hf.coordinates x
  have hxJ : (x : E) ∈ J.space := hV0J ⟨x, hxV0, rfl⟩
  have hBJ : IsOpen ((Subtype.val : J.space → E) ⁻¹' B) :=
    hBo.preimage (continuous_subtype_val.subtype_mk (fun z ↦ hJD z.property))
  obtain ⟨N, W, hN, hNJ, hW, hxW, hWN, hNB'⟩ :=
    J.exists_relative_polyhedral_neighborhood hJ ⟨x, hxJ⟩ hBJ hx
  have hNB : N.space ⊆ B := fun z hz ↦
    hNB' (show (⟨z, hNJ hz⟩ : J.space) ∈ (Subtype.val : J.space → E) ⁻¹' N.space from hz)
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  let V : Set S := V0 ∩ (Subtype.val : S → E) ⁻¹' O
  have hVo : IsOpen V := hV0.inter (hO.preimage continuous_subtype_val)
  have hxV : x ∈ V := ⟨hxV0, hOW.symm.subset hxW⟩
  have hVN : Subtype.val '' V ⊆ N.space := by
    rintro z ⟨y, ⟨hyV0, hyO⟩, rfl⟩
    have hyJ : (y : E) ∈ J.space := hV0J ⟨y, hyV0, rfl⟩
    exact hWN ⟨⟨y, hyJ⟩, hOW.subset hyO, rfl⟩
  have hfN := hf.restrict_finite N hN (hNJ.trans hJD)
  have hcoords : FinitePiecewiseAffineOn (C.chart ∘ f) N.space :=
    hfN.finitePiecewiseAffineOn_compatible_chart_finite_source N hN C.chart C.compatible
      (fun z hz ↦ hBT z (hNB hz))
  have hinj : InjOn (C.chart ∘ f) N.space := by
    intro u hu v hv huv
    have hfu : f u = f v := C.chart.injOn (hBT u (hNB hu)) (hBT v (hNB hv)) huv
    exact congrArg Subtype.val (hBe.injective
      (show (fun z : B ↦ f z) ⟨u, hNB hu⟩ = (fun z : B ↦ f z) ⟨v, hNB hv⟩ from hfu))
  obtain ⟨H, hH, hHval⟩ := hcoords.exists_homeomorph_image hinj
  refine ⟨N, V, hN, hNB, hVo, hxV, hVN, hcoords, H, hH, hH.symm, hHval, ?_⟩
  intro w
  have h := hHval (H.symm w)
  rw [H.apply_symm_apply] at h
  exact h.symm

end PoincareConjecture.M76.Dehn.Annuli
