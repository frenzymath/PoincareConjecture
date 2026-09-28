import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.FiniteLevelPartition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.OriginalPLIdentity
import PoincareConjecture.Proofs.M76.Rigidity.EmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Periodicity









set_option autoImplicit false
open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem exists_standard_relative_parameter
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (x : R) :
    ∃ (K : SimplicialComplex ℝ V3) (q : V3 → R) (z : K.space),
      K.faces.Finite ∧ ContinuousOn q K.space ∧
      Topology.IsEmbedding (fun u : K.space => q u) ∧ q z = x ∧
      range (fun u : K.space => q u) ∈ 𝓝 x ∧
      PolyhedralPLInCharts d (fun u => (q u : X)) K.space := by
  classical
  obtain ⟨i, _, K, V, _, hK, hV, hxV, _, hVi, hVK, hKt, hKR, _, _⟩ :=
    (standard_chartwisePLMap_identity hd).coordinates x (mem_univ x)
  have hinR (u : V3) (hu : u ∈ K.space) : (d i).symm u ∈ R := by
    obtain ⟨y, _, hy⟩ := hKR hu
    exact hy ▸ y.property
  let q : V3 → R := fun u => if hu : u ∈ K.space then ⟨(d i).symm u, hinR u hu⟩ else x
  have hqval (u : V3) (hu : u ∈ K.space) : (q u : X) = (d i).symm u := by simp [q, hu]
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (((d i).symm.continuousOn.mono hKt).congr hqval)
  have hi : Topology.IsEmbedding (fun u : K.space => (q u : X)) := by
    have heq : (fun u : K.space => (q u : X)) = fun u : K.space => (d i).symm u :=
      funext (fun u => hqval u u.property)
    rw [heq]
    exact (d i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun u : K.space => q u) :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hi
  have hxK : d i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  let z : K.space := ⟨d i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((hqval _ hxK).trans ((d i).left_inv (hVi hxV)))
  have hVrange : V ⊆ range (fun u : K.space => q u) := by
    intro y hy
    have hyK := hVK ⟨y, hy, rfl⟩
    exact ⟨⟨d i y, hyK⟩, Subtype.ext ((hqval _ hyK).trans ((d i).left_inv (hVi hy)))⟩
  have hqPL : PolyhedralPLInCharts d (fun u => (q u : X)) K.space := by
    apply (polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK)
      i hKt).congr
    intro u hu
    exact (hqval u hu).symm
  exact ⟨K, q, z, hK, hq, hiq, hqz,
    Filter.mem_of_superset (hV.mem_nhds hxV) hVrange, hqPL⟩



theorem exists_standard_parameter_avoiding_phase
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (x : R) (c : ℝ)
    (hx : sourcePhase (ContinuousMap.id H)
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ≠ (c : C)) :
    ∃ (K : SimplicialComplex ℝ V3) (q : V3 → R) (z : K.space),
      K.faces.Finite ∧ ContinuousOn q K.space ∧
      Topology.IsEmbedding (fun u : K.space => q u) ∧ q z = x ∧
      range (fun u : K.space => q u) ∈ 𝓝 x ∧
      PolyhedralPLInCharts d (fun u => (q u : X)) K.space ∧
      ∀ u ∈ K.space, sourcePhase (ContinuousMap.id H)
        (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q u)) ≠ (c : C) := by
  obtain ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL⟩ :=
    exists_standard_relative_parameter hd x
  let phase : C(R, C) := (sourcePhase (ContinuousMap.id H)).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  let O : Set K.space := (fun y : K.space => phase (q y)) ⁻¹' {(c : C)}ᶜ
  have hO : IsOpen O := isOpen_compl_singleton.preimage (phase.continuous.comp hq.domRestrict)
  have hzO : z ∈ O := by change phase (q z) ≠ (c : C); rw [hqz]; exact hx
  obtain ⟨N, V, hN, hNK, hV, hzV, hVN, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK z hO hzO
  have hzN : (z : V3) ∈ N.space := hVN ⟨z, hzV, rfl⟩
  have hnear : range (fun u : N.space => q u) ∈ 𝓝 x := by
    obtain ⟨U, hU, hUV⟩ := hiq.isInducing.image_eq_isOpen_inter_range hV
    have hxU : x ∈ U := by
      rw [← hqz]
      exact (hUV.subset ⟨z, hzV, rfl⟩).1
    apply Filter.mem_of_superset (Filter.inter_mem (hU.mem_nhds hxU) hrange)
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hUV.symm.subset hy
    exact ⟨⟨u, hVN ⟨u, hu, rfl⟩⟩, rfl⟩
  refine ⟨N, q, ⟨z, hzN⟩, hN, hq.mono hNK,
    hiq.comp (Topology.IsEmbedding.inclusion hNK), hqz, hnear,
    hqPL.restrict_finite N hN hNK, ?_⟩
  intro u hu
  exact hNO (show (⟨u, hNK hu⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hu)



theorem exists_finite_standard_slab_parameter_cover
    {V β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (a b : ℝ) (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (q : V → R) (hqPL : PolyhedralPLInCharts d (fun u => (q u : X)) K.space)
    (hseam : ∀ u ∈ K.space, sourcePhase (ContinuousMap.id H)
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q u)) ≠ (a : C)) :
    ∃ J : Set (SimplicialComplex ℝ V), J.Finite ∧
      (∀ N ∈ J, N.faces.Finite ∧ N.space ⊆ K.space ∧
        (MapsTo (fun u => (q u : X)) N.space (sourceSlab (ContinuousMap.id H) a b) ∨
          MapsTo (fun u => (q u : X)) N.space (sourceSlab (ContinuousMap.id H) b (a + p)))) ∧
      K.space ⊆ ⋃ N ∈ J, N.space := by
  let phase : C(R, C) := (sourcePhase (ContinuousMap.id H)).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  let A := AddCircle.openPartialHomeomorphCoe p a
  let t : V → ℝ := fun u => A.symm (phase (q u))
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have htPL : FinitePiecewiseAffineOn t K.space :=
    finitePiecewiseAffineOn_sourcePhase_coordinate hd (ContinuousMap.id H)
      (standard_chartwisePLMap_identity hd) K hK q hq hqPL a hseam
  have ht (u : V) (hu : u ∈ K.space) : t u ∈ Ioo a (a + p) ∧ (t u : C) = phase (q u) :=
    ⟨A.map_target (hseam u hu), A.right_inv (hseam u hu)⟩
  obtain ⟨J, hJ, hpieces, hcover⟩ := exists_finite_three_level_cover htPL (le_refl b)
  refine ⟨J, hJ, ?_, hcover⟩
  intro N hNJ
  obtain ⟨hN, hNK, hcase⟩ := hpieces N hNJ
  refine ⟨hN, hNK, ?_⟩
  have hlow (hlow : MapsTo t N.space (Iic b)) :
      MapsTo (fun u => (q u : X)) N.space (sourceSlab (ContinuousMap.id H) a b) := by
    intro u hu
    apply (mem_sourceSlab_iff (ContinuousMap.id H) a b (q u)).mpr
    exact ⟨t u, ⟨(ht u (hNK hu)).1.1.le, hlow hu⟩, (ht u (hNK hu)).2⟩
  rcases hcase with h | h | h
  · exact Or.inl (hlow h)
  · exact Or.inl (hlow (fun u hu => (h hu).2))
  · right
    intro u hu
    apply (mem_sourceSlab_iff (ContinuousMap.id H) b (a + p) (q u)).mpr
    exact ⟨t u, ⟨h hu, (ht u (hNK hu)).1.2.le⟩, (ht u (hNK hu)).2⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
