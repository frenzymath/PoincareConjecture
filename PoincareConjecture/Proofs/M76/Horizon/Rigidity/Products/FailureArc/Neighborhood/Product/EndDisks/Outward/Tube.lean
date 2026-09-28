import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceBox



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem original_tube_end_slice_subset_component
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    (fun q : P2 => U.map (q,t)) '' transverseSquare 1 ⊆
      connectedComponentIn (frontier R) (U.map ((0,0),t)) := by
  have hc : ContinuousOn (fun q : P2 => U.map (q,t)) (transverseSquare 1) :=
    U.pl.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun q hq => ⟨hq,t.property⟩)
  apply ((((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).isPreconnected).image _ hc).subset_connectedComponentIn
  · exact ⟨(0,0),by norm_num [transverseSquare],rfl⟩
  · rintro x ⟨q,hq,rfl⟩
    exact (U.frontier_iff _ ⟨hq,t.property⟩).mpr ht

theorem original_tube_lateral_mem_closure_endpoint_outside
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1)
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    {q : P2} (hq : q ∈ frontier (transverseSquare r))
    {B : Set X} (hB : IsClosed B) (hqB : U.map (q,t) ∉ B)
    (x : connectedComponentIn (frontier R) (U.map ((0,0),t)))
    (hx : (x : X) = U.map (q,t)) :
    x ∈ closure ((Subtype.val : connectedComponentIn (frontier R)
      (U.map ((0,0),t)) → X) ⁻¹' (U.map '' closedTube r ∪ B)ᶜ) := by
  let V : Set P2 := interior (transverseSquare 1)
  have hqsmall : q ∈ transverseSquare r := (isClosed_transverseSquare r).frontier_subset hq
  have hqV : q ∈ V := by
    change q ∈ interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
    rw [interior_prod_eq,interior_Icc]
    exact ⟨⟨by linarith [hqsmall.1.1],by linarith [hqsmall.1.2]⟩,
      ⟨by linarith [hqsmall.2.1],by linarith [hqsmall.2.2]⟩⟩
  let F := connectedComponentIn (frontier R) (U.map ((0,0),t))
  have hplace (p : V) : U.map (p,t) ∈ F :=
    original_tube_end_slice_subset_component U t ht ⟨p,interior_subset p.property,rfl⟩
  let g : V → F := fun p => ⟨U.map (p,t),hplace p⟩
  have hgc : Continuous g := by
    apply Continuous.subtype_mk
    exact U.pl.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun p => ⟨interior_subset p.property,t.property⟩)
  have hqcl : (⟨q,hqV⟩ : V) ∈ closure ((Subtype.val : V → P2) ⁻¹' (transverseSquare r)ᶜ) := by
    apply isOpen_interior.isOpenMap_subtype_val.preimage_closure_subset_closure_preimage
    exact ((frontier_eq_closure_inter_closure (s := transverseSquare r)).subset hq).2
  have him : MapsTo g ((Subtype.val : V → P2) ⁻¹' (transverseSquare r)ᶜ)
      ((Subtype.val : F → X) ⁻¹' (U.map '' closedTube r)ᶜ) := by
    intro p hp hmem
    obtain ⟨z,hz,hzp⟩ := hmem
    have heq : z = ((p : P2),(t : ℝ)) := congrArg Subtype.val
      (U.embedding.injective (a₁ := ⟨z,closedTube_subset hr1.le hz⟩)
        (a₂ := ⟨((p : P2),(t : ℝ)),⟨interior_subset p.property,t.property⟩⟩) hzp)
    exact hp (heq ▸ hz).1
  have hgcl : g ⟨q,hqV⟩ ∈ closure ((Subtype.val : F → X) ⁻¹' (U.map '' closedTube r)ᶜ) :=
    hgc.continuousAt.continuousWithinAt.mem_closure hqcl him
  have hgx : g ⟨q,hqV⟩ = x := Subtype.ext hx.symm
  rw [hgx] at hgcl
  have hBo : IsOpen ((Subtype.val : F → X) ⁻¹' Bᶜ) := hB.isOpen_compl.preimage continuous_subtype_val
  have hxB : x ∈ (Subtype.val : F → X) ⁻¹' Bᶜ := by
    simpa only [mem_preimage,mem_compl_iff,hx] using hqB
  have hfinal := hBo.inter_closure ⟨hxB,hgcl⟩
  apply closure_mono ?_ hfinal
  intro y hy
  exact fun h => h.elim hy.2 hy.1

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
