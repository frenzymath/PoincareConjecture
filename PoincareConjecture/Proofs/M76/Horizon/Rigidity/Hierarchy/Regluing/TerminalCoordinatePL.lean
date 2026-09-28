import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoundaryMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskFamilyInstallation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyParameterPL
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem polyhedralPL_hamiltonZero_box_projection
    {κ : Type*} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite) :
    PolyhedralPLInCharts d (fun z : (ℝ × ℝ) × ℝ =>
      (Q0).symm ((((z.1.1 : C0), (z.1.2 : C0))), (z.2 : C0))) K.space := by
  let fst0 := ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ
  let v : ((ℝ × ℝ) × ℝ) →L[ℝ] V3 := ContinuousLinearMap.pi
    ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp fst0,
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp fst0,
      ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ]
  let a : ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((0 : ((ℝ × ℝ) × ℝ) →L[ℝ] (Fin 0 → ℝ)).prod v).toContinuousAffineMap
  apply (hd.polyhedralPL_projection
    (show FinitePiecewiseAffineOn a K.space from ⟨K, hK, rfl, K.affineOnFaces_affine a⟩)).congr
  intro z hz
  apply (Q0).injective
  rw [(Q0).apply_symm_apply]
  rfl

theorem hamiltonZero_box_projection_injOn
    {u v a b alpha beta : ℝ}
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p) :
    InjOn (fun z : (ℝ × ℝ) × ℝ =>
      (Q0).symm ((((z.1.1 : C0), (z.1.2 : C0))), (z.2 : C0)))
      ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
  intro x hx y hy hxy
  have h := (Q0).symm.injective hxy
  have hcoe {l r s t : ℝ} (hgap : r < l + p) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
      (heq : (s : C0) = (t : C0)) : s = t :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico ⟨hs.1, hs.2.trans_lt hgap⟩
      ⟨ht.1, ht.2.trans_lt hgap⟩).mp heq
  exact Prod.ext (Prod.ext (hcoe hthird hx.1.1 hy.1.1 (congrArg (fun z => z.1.1) h))
    (hcoe hsecond hx.1.2 hy.1.2 (congrArg (fun z => z.1.2) h)))
    (hcoe hfirst hx.2 hy.2 (congrArg Prod.snd h))



theorem ChartwisePLMap.finitePL_hamiltonZero_box_lift
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (j : E → X0) (hj : PolyhedralPLInCharts e j K.space)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (lift : E → (ℝ × ℝ) × ℝ) (hcont : ContinuousOn lift K.space)
    (hbox : MapsTo lift K.space ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta))
    (hvalue : ∀ z ∈ K.space, Q0 (hamiltonZeroAmbientMap phi (j z)) =
      ((((lift z).1.1 : C0), ((lift z).1.2 : C0)), ((lift z).2 : C0))) :
    FinitePiecewiseAffineOn lift K.space := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBBox, _⟩, _⟩, _⟩ :=
    ((isFinitePLBallPair_Icc huv).prod (isFinitePLBallPair_Icc hab)).prod
      (isFinitePLBallPair_Icc halpha)
  have hprojection := polyhedralPL_hamiltonZero_box_projection hd B hB
  rw [hBBox] at hprojection
  apply hprojection.finitePiecewiseAffineOn_lift hphi.target_domain.compatible
    (hamiltonZero_box_projection_injOn hthird hsecond hfirst) K hK hcont hbox
  apply (hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hj).congr
  intro z hz
  dsimp only [Function.comp_apply]
  apply (Q0).injective
  rw [(Q0).apply_symm_apply]
  exact hvalue z hz



theorem exists_hamiltonZero_finitePL_boundary_coordinates
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N) (hne : N.Nonempty)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (boundaryMap : C(frontier N, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier N, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : (ℝ × ℝ) × ℝ).1.1) : C0),
        (((boundaryMap x : (ℝ × ℝ) × ℝ).1.2) : C0)),
        (((boundaryMap x : (ℝ × ℝ) × ℝ).2) : C0))) :
    ∃ (s : Finset N) (A : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : A.space ≃ₜ frontier N) (j : (s → ℝ × V3) → X0)
      (lift : (s → ℝ × V3) → (ℝ × ℝ) × ℝ),
      A.faces.Finite ∧ PolyhedralPLInCharts e j A.space ∧
      (∀ z : A.space, j z = (HB z : X0)) ∧
      FinitePiecewiseAffineOn lift A.space ∧
      ∀ z : A.space, lift z = (boundaryMap (HB z) : (ℝ × ℝ) × ℝ) := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨s, F, K, A, H, inverse, HB, _, _, hK, hAK, hA, _, _, _, _, _, _,
    hinverse, hHB, _, _, _⟩ := he.exists_original_frontier_surface_model hN hne
  let j : (s → ℝ × V3) → X0 := fun z => inverse z
  have hj : PolyhedralPLInCharts e j A.space :=
    hinverse.restrict_finite A hA (SimplicialComplex.space_subset_of_le hAK)
  let lift (z : s → ℝ × V3) : (ℝ × ℝ) × ℝ :=
    if hz : z ∈ A.space then boundaryMap (HB ⟨z, hz⟩) else 0
  have hlift (z : A.space) : lift z = (boundaryMap (HB z) : (ℝ × ℝ) × ℝ) := by
    simp only [lift, dif_pos z.property]
  have hcont : ContinuousOn lift A.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp (boundaryMap.continuous.comp HB.continuous)).congr
      (fun z => (hlift z).symm)
  have hbox : MapsTo lift A.space ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
    intro z hz
    rw [hlift ⟨z, hz⟩]
    exact ((isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc).frontier_subset
      (boundaryMap (HB ⟨z, hz⟩)).property
  refine ⟨s, A, HB, j, lift, hA, hj, fun z => (hHB z).symm, ?_, hlift⟩
  apply hphi.finitePL_hamiltonZero_box_lift hd A hA j hj huv hab halpha
    hthird hsecond hfirst lift hcont hbox
  intro z hz
  rw [hlift ⟨z, hz⟩, show j z = (HB ⟨z, hz⟩ : X0) from (hHB ⟨z, hz⟩).symm]
  exact hvalue (HB ⟨z, hz⟩)

end PoincareConjecture.M76
