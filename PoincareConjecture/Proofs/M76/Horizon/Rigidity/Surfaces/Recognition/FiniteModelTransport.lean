import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Recognition.OriginalFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph







set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

namespace PeriodicSquare

noncomputable def SourceSquareMap.transport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {J : SimplicialComplex ℝ F}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ J.space) (hH : H.IsFinitePL) :
    SourceSquareMap p J := by
  refine {
    map := (⟨H, H.continuous⟩ : C(K.space, J.space)).comp M.map
    surjective := H.surjective.comp M.surjective
    fibers := ?_
    finite_piecewise_affine := ?_ }
  · intro z w
    exact H.injective.eq_iff.trans (M.fibers z w)
  · obtain ⟨f, hf, hvalue⟩ := hH
    obtain ⟨u, hu, huvalue⟩ := M.finite_piecewise_affine
    have hmap : MapsTo u (squareCarrier p) K.space := by
      intro z hz
      let w : Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      rw [show u z = (M.map w : E) from huvalue w]
      exact (M.map w).property
    refine ⟨f ∘ u, hf.comp hu hmap, ?_⟩
    intro z
    exact (congrArg f (huvalue z)).trans (hvalue (M.map z)).symm

end PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem PLDomain.nonempty_sourceSquareMap_of_original_component_model
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3} {D : Set X0}
    (he : PLDomain e D) (hD : IsCompact D) (x : X0) (hx : x ∈ frontier D)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier D) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier D) x, X0)) ⟨x, mem_connectedComponentIn hx⟩))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E → X0) (hf : PolyhedralPLInCharts e f K.space)
    (H : K.space ≃ₜ connectedComponentIn (frontier D) x)
    (hH : ∀ z : K.space, f z = (H z : X0)) :
    Nonempty (PeriodicSquare.SourceSquareMap 64 K) := by
  classical
  let : Fact (0 < (64 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨s, coords, J, g, G, _, hcoordsPL, _, _, hG, hinverse, ⟨M⟩⟩ :=
    he.exists_original_frontier_torus_square_model e he.cover he.compatible hD x hx hnt hinj
  let T : K.space ≃ₜ J.space := H.trans G.symm
  have hT : T.IsFinitePL := by
    refine ⟨coords ∘ f, hf.finitePiecewiseAffineOn_comp K hK hcoordsPL, ?_⟩
    intro z
    change (G.symm (H z) : s → ℝ × V3) = coords (f z)
    calc
      (G.symm (H z) : s → ℝ × V3) = coords (g (G.symm (H z))) :=
        (hinverse _ (G.symm (H z)).property).symm
      _ = coords (H z) := by rw [← hG, G.apply_symm_apply]
      _ = coords (f z) := congrArg coords (hH z).symm
  exact ⟨M.transport T.symm hT.symm⟩

end PoincareConjecture.M76
