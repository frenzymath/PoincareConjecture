import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteFrontierComponents
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem exists_original_frontier_components
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F : Set X}
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (H : N ≃ₜ K.space) (g : E → N)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (HB : A.space ≃ₜ frontier N) (hHB : ∀ z : A.space, (HB z : X) = (g z : X))
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty) :
    ∃ (n : ℕ) (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (S : Fin n → Set X), 0 < n ∧
      (∀ i, S i = (fun z => (g z : X)) '' (A.edgeComponentComplex (pick i)).space) ∧
      (⋃ i, S i) = F ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      ∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        (∀ x ∈ S i, connectedComponentIn F x = S i) ∧
        PolyhedralPLInCharts e (fun z => (g z : X))
          (A.edgeComponentComplex (pick i)).space ∧
        ∃ HC : (A.edgeComponentComplex (pick i)).space ≃ₜ S i,
          ∀ z, (HC z : X) = (g z : X) := by
  classical
  have hA : A.faces.Finite := hK.subset hAK
  let : Finite A.vertices := (A.finite_vertices_of_finite_faces hA).to_subtype
  let q : E → X := fun z => g z
  let S0 (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) : Set X :=
    q '' (A.edgeComponentComplex c).space
  have hsub (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      (A.edgeComponentComplex c).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le ((A.edgeComponentComplex_le c).trans hAK)
  have hfinite (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      (A.edgeComponentComplex c).faces.Finite := hA.subset (A.edgeComponentComplex_le c)
  have hcompact (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      IsCompact (S0 c) :=
    ((A.edgeComponentComplex c).isCompact_space_of_finite (hfinite c)).image_of_continuousOn
      (hgPL.continuousOn.mono (hsub c))
  have hconn (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      IsConnected (S0 c) :=
    (A.edgeComponentComplex_isPathConnected c).isConnected.image q
      (hgPL.continuousOn.mono (hsub c))
  have hinj : InjOn q K.space := by
    intro x hx y hy hxy
    have hinv : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hinv)
  have hdisjoint : Pairwise fun c d => Disjoint (S0 c) (S0 d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro x ⟨u, hu, hux⟩ ⟨v, hv, hvx⟩
    have huv := hinj (hsub c hu) (hsub d hv) (hux.trans hvx.symm)
    exact disjoint_left.mp (A.pairwise_disjoint_edgeComponentComplex_space hcd)
      hu (huv.symm ▸ hv)
  have hboundary : q '' A.space = frontier N := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      change (g z : X) ∈ frontier N
      rw [← hHB ⟨z, hz⟩]
      exact (HB ⟨z, hz⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := HB.surjective ⟨x, hx⟩
      exact ⟨z, z.property, (hHB z).symm.trans (congrArg Subtype.val hz)⟩
  have hunion : (⋃ c, S0 c) = frontier N := by
    change (⋃ c, q '' (A.edgeComponentComplex c).space) = frontier N
    rw [← image_iUnion, A.iUnion_edgeComponentComplex_space, hboundary]
  obtain ⟨n, pick, hn, hselected, hcomponents⟩ :=
    exists_indexed_components_of_closed_partition S0 (fun c => (hcompact c).isClosed)
      hconn hdisjoint hB hF hBF (hunion.trans hfront) hFne
  refine ⟨n, pick, fun i => S0 (pick i), hn, fun _ => rfl, hselected,
    fun _ _ hij => hdisjoint (fun h => hij (pick.injective h)), ?_⟩
  intro i
  have hSi : S0 (pick i) ⊆ F :=
    fun _ hx => hselected.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hPL := hgPL.restrict_finite (A.edgeComponentComplex (pick i))
    (hfinite (pick i)) (hsub (pick i))
  let T := (A.edgeComponentComplex (pick i)).space
  let : CompactSpace T := isCompact_iff_compactSpace.mp
    ((A.edgeComponentComplex (pick i)).isCompact_space_of_finite (hfinite (pick i)))
  let HC0 : T ≃ q '' T := Equiv.Set.imageOfInjOn q T (hinj.mono (hsub (pick i)))
  have hHC0 : Continuous HC0 :=
    (hgPL.continuousOn.mono (hsub (pick i))).domRestrict.subtype_mk _
  let HC : T ≃ₜ q '' T := HC0.toHomeomorphOfContinuousClosed hHC0 hHC0.isClosedMap
  exact ⟨hcompact (pick i), hconn (pick i), hSi, hcomponents i, hPL, HC, fun _ => rfl⟩

end PoincareConjecture.M76
