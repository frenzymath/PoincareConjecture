import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.OriginalComponent
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.OriginalComponentGenusComparison

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

private theorem based_group_data_of_set_eq {S T : Set X0} (h : S = T)
    (x : S) (y : T) (hxy : (x : X0) = y)
    (hnt : Nontrivial (FundamentalGroup S x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    Nontrivial (FundamentalGroup T y) ∧ Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(T, X0)) y) := by
  subst T
  have heq : x = y := Subtype.ext hxy
  subst y
  exact ⟨hnt, hinj⟩

private theorem whole_phase_component_eq
    {B F S : Set X0} (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hS : IsConnected S) (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S) (x : S) :
    connectedComponentIn (B ∪ F) x = S := by
  have hx : (x : X0) ∈ B ∪ F := Or.inr (hSF x.property)
  have hC := isConnected_connectedComponentIn_iff.mpr hx
  have hCF : connectedComponentIn (B ∪ F) x ⊆ F := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC.isPreconnected
      B F hB hF (connectedComponentIn_subset _ _) (by
        rw [disjoint_iff_inter_eq_empty.mp hBF, inter_empty]) with hb | hf
    · exact False.elim (disjoint_left.mp hBF (hb (mem_connectedComponentIn hx))
        (hSF x.property))
    · exact hf
  apply Subset.antisymm
  · exact (hC.isPreconnected.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hCF).trans (hcomponent x x.property).subset
  · exact hS.isPreconnected.subset_connectedComponentIn x.property
      (hSF.trans subset_union_right)

open Classical in
theorem FrontierResidualModel.euler_zero_of_ambient_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D N B F : Set X0} (he : PLDomain e D) (hD : IsCompact D)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier D = B ∪ F)
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (x : M.components i) (hnt : Nontrivial (FundamentalGroup (M.components i) x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(M.components i, X0)) x)) :
    (M.complex.edgeComponentComplex (M.pick i)).surfaceEulerCount = 0 := by
  have hx : (x : X0) ∈ frontier D := hfront.symm ▸ Or.inr ((M.component i).2.2.1 x.property)
  have hcomponent : connectedComponentIn (frontier D) x = M.components i := by
    rw [hfront]
    exact whole_phase_component_eq hB hF hBF (M.component i).2.1
      (M.component i).2.2.1 (M.component i).2.2.2 x
  obtain ⟨hnt', hinj'⟩ := based_group_data_of_set_eq hcomponent.symm x
    ⟨x, mem_connectedComponentIn hx⟩ rfl hnt hinj
  obtain ⟨s, phi, J, g, H, _, hphiPL, hJ, hdimJ, _, hH, hinverse, hzero⟩ :=
    he.exists_original_component_euler_zero e hcover hcompat hD x hx hnt' hinj'
  have himage : g '' J.space = connectedComponentIn (frontier D) x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hH ⟨z, hz⟩) ▸ (H ⟨z, hz⟩).property
    · intro hy
      obtain ⟨z, hz⟩ := H.surjective ⟨y, hy⟩
      exact ⟨z, z.property, (hH z).symm.trans (congrArg Subtype.val hz)⟩
  have hphii : InjOn phi (connectedComponentIn (frontier D) x) := by
    intro y hy z hz heq
    obtain ⟨a, ha, rfl⟩ := himage.symm.subset hy
    obtain ⟨b, hb, rfl⟩ := himage.symm.subset hz
    rw [hinverse a ha, hinverse b hb] at heq
    exact congrArg g heq
  let A := M.complex.edgeComponentComplex (M.pick i)
  have hA : A.faces.Finite := M.finite.subset (M.complex.edgeComponentComplex_le _)
  have hsub : A.space ⊆ M.complex.space :=
    SimplicialComplex.space_subset_of_le (M.complex.edgeComponentComplex_le _)
  have hEuler := original_component_surfaceEulerCount_eq A J hA hJ
    (fun t ht => M.dimension t (M.complex.edgeComponentComplex_le _ ht)) hdimJ
    M.map g phi (M.pl.restrict_finite A hA hsub) (M.injective.mono hsub)
    ((M.images i).symm.trans hcomponent.symm) himage hphiPL hphii hinverse
  exact hEuler.trans hzero

theorem FrontierResidualModel.residual_eq_two_of_ambient_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D N B F : Set X0} (he : PLDomain e D) (hD : IsCompact D)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier D = B ∪ F)
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (x : M.components i) (hnt : Nontrivial (FundamentalGroup (M.components i) x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(M.components i, X0)) x)) :
    M.residual i = 2 :=
  M.residual_eq_two_of_character_rank i
    (M.euler_zero_of_ambient_injective e hcover hcompat he hD hB hF hBF hfront i x hnt hinj)

theorem FrontierResidualModel.original_torus_candidate_of_ambient_injective
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D N B F : Set X0} (he : PLDomain e D) (hD : IsCompact D)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier D = B ∪ F)
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (x : M.components i) (hnt : Nontrivial (FundamentalGroup (M.components i) x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(M.components i, X0)) x)) :
    ∃ C : OriginalTorusEulerCandidate e N F, C.model = M ∧ C.component.val = i.val :=
  ⟨⟨M, i, M.residual_eq_two_of_ambient_injective e hcover hcompat he hD
    hB hF hBF hfront i x hnt hinj⟩, rfl, rfl⟩

end PoincareConjecture.M76
