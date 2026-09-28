




module

public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.FundamentalGroup
public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.SemilocallySimplyConnected.Basic
public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.PathHomotopy
















namespace Poincare.Topology

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set _root_.Topology

variable {X : Type*} [TopologicalSpace X]






public def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ (base : U),
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) base).range = ⊥


public theorem SemilocallySimplyConnectedAt.of_simplyConnectedSpace
    [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun base ↦ by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient base.val base.val) _ _⟩



public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) := by
  constructor
  ·
    intro ⟨U, hU_nhd, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hx_in_V⟩ := mem_nhds_iff.mp hU_nhd
    refine ⟨V, hV_open, hx_in_V, ?_⟩
    intro u γ hγ_range
    have hγ_mem : ∀ t, γ t ∈ U := fun t ↦ hVU (hγ_range ⟨t, rfl⟩)
    have h := (FundamentalGroup.map_range_eq_bot_iff ⟨Subtype.val, continuous_subtype_val⟩
      (⟨u, γ.source ▸ hγ_mem 0⟩ : U)).mp (hU_loops _) (γ.codRestrict hγ_mem)
    rwa [Path.map_codRestrict] at h
  ·
    intro ⟨U, hU_open, hx_in_U, hU_loops_null⟩
    refine ⟨U, hU_open.mem_nhds hx_in_U, fun base ↦
      (FundamentalGroup.map_range_eq_bot_iff ⟨Subtype.val, continuous_subtype_val⟩ base).mpr fun γ ↦
        hU_loops_null (γ.map continuous_subtype_val) ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (γ t).property



public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  constructor
  · intro ⟨U, hU_open, hx_in_U, hU_loops⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u u' γ γ' hγ hγ'

    have hloop : range (γ.trans γ'.symm) ⊆ U := by
      intro y hy
      simp only [Path.trans_range, Path.symm_range] at hy
      exact hy.elim (fun h ↦ hγ h) (fun h ↦ hγ' h)
    have hnull := hU_loops (γ.trans γ'.symm) hloop
    exact Path.Homotopic.of_trans_symm hnull
  · intro ⟨U, hU_open, hx_in_U, hU_paths⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u γ hγ
    have hrefl : range (Path.refl u) ⊆ U := by
      simp only [Path.refl_range, singleton_subset_iff]
      exact hγ ⟨0, γ.source⟩
    exact hU_paths γ (Path.refl u) hγ hrefl



variable {s t : Set X} {x : X}



public def SemilocallySimplyConnectedOn (s : Set X) : Prop :=
  ∀ x ∈ s, SemilocallySimplyConnectedAt x



public theorem SemilocallySimplyConnectedOn.at (h : SemilocallySimplyConnectedOn s) (hx : x ∈ s) :
    SemilocallySimplyConnectedAt x :=
  h x hx


public theorem SemilocallySimplyConnectedOn.mono (h : SemilocallySimplyConnectedOn t)
    (hst : s ⊆ t) : SemilocallySimplyConnectedOn s :=
  fun x hx ↦ h x (hst hx)






public def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q



public theorem IsPathHomotopyTrivial.apply {U : Set X} (hU : IsPathHomotopyTrivial U)
    ⦃a b : X⦄ (p q : Path a b) (hp : range p ⊆ U) (hq : range q ⊆ U) :
    Path.Homotopic p q :=
  hU p q hp hq



public theorem semilocallySimplyConnectedOn_iff :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff




public theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff_paths














public theorem SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x := by
  obtain ⟨U, hUopen, hxU, hloop⟩ :=
    SemilocallySimplyConnectedSpace.exists_isOpen_mem_nhds_loops_nullhomotopic x
  refine semilocallySimplyConnectedAt_iff.mpr
    ⟨pathComponentIn U x, hUopen.pathComponentIn x, mem_pathComponentIn_self hxU, ?_⟩
  intro u γ hγ

  have hu : u ∈ pathComponentIn U x := hγ ⟨0, γ.source⟩

  let hjoin : JoinedIn (pathComponentIn U x) x u :=
    (isPathConnected_pathComponentIn hxU).joinedIn _ (mem_pathComponentIn_self hxU) _ hu
  let δ : Path x u := hjoin.somePath
  have hδ : Set.range δ ⊆ pathComponentIn U x := Set.range_subset_iff.mpr hjoin.somePath_mem

  have hδU : ∀ s, δ s ∈ pathComponentIn U x := fun s ↦ hδ ⟨s, rfl⟩
  have hsub : Set.range ((δ.trans γ).trans δ.symm) ⊆ pathComponentIn U x := by
    rw [Path.trans_range, Path.trans_range, Path.symm_range]
    exact Set.union_subset (Set.union_subset (fun _ ⟨s, hs⟩ ↦ hs ▸ hδU s) hγ)
      (fun _ ⟨s, hs⟩ ↦ hs ▸ hδU s)
  have hconj : ((δ.trans γ).trans δ.symm).Homotopic (Path.refl x) :=
    hloop _ fun t ↦ pathComponentIn_subset (hsub ⟨t, rfl⟩)


  have hδγ : (δ.trans γ).Homotopic δ := Path.Homotopic.of_trans_symm hconj

  exact Path.Homotopic.trans_left_cancel (hδγ.trans (Path.Homotopic.trans_refl δ).symm)





public theorem SemilocallySimplyConnectedSpace.of_forall_semilocallySimplyConnectedAt
    (h : ∀ x : X, SemilocallySimplyConnectedAt x) : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    obtain ⟨U, hUopen, hxU, hloop⟩ := semilocallySimplyConnectedAt_iff.mp (h x)
    exact ⟨U, hUopen.mem_nhds hxU, fun γ hγ ↦ hloop γ (range_subset_iff.mpr hγ)⟩




public theorem semilocallySimplyConnectedSpace_iff_forall_semilocallySimplyConnectedAt
    [LocallyPathConnectedSpace X] :
    SemilocallySimplyConnectedSpace X ↔ ∀ x : X, SemilocallySimplyConnectedAt x := by
  refine ⟨fun _ x ↦ .of_semilocallySimplyConnectedSpace x,
    SemilocallySimplyConnectedSpace.of_forall_semilocallySimplyConnectedAt⟩



public theorem SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (s : Set X) :
    SemilocallySimplyConnectedOn s :=
  fun x _ ↦ .of_semilocallySimplyConnectedSpace x









public theorem SemilocallySimplyConnectedAt.exists_isOpen_mem_isPathHomotopyTrivial {x : X}
    (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathHomotopyTrivial U :=
  semilocallySimplyConnectedAt_iff_paths.mp h



public theorem exists_isOpen_mem_isPathHomotopyTrivial
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathHomotopyTrivial U := by
  have hx := SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace x
  exact hx.exists_isOpen_mem_isPathHomotopyTrivial




public theorem SemilocallySimplyConnectedAt.exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial
    [LocallyPathConnectedSpace X] {x : X} (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by



  obtain ⟨V, hV_open, hx_in_V, hV_slsc⟩ := h.exists_isOpen_mem_isPathHomotopyTrivial
  refine ⟨pathComponentIn V x, hV_open.pathComponentIn x, mem_pathComponentIn_self hx_in_V,
    isPathConnected_pathComponentIn hx_in_V, fun _ _ p q hp hq ↦ ?_⟩
  exact hV_slsc.apply p q (hp.trans pathComponentIn_subset) (hq.trans pathComponentIn_subset)



public theorem exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  have hx := SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace x
  exact hx.exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial

end

end Poincare.Topology
