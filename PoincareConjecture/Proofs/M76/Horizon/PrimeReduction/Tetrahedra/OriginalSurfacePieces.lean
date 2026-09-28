import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfaceComplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ComponentMembership
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent









set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_sphere_pieces_in_face
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {t : Finset E} (ht : t ∈ K.faces) :
    ∃ γ : Type u, Finite γ ∧ ∃ (C : γ → SimplicialComplex ℝ E) (P : γ → Set X),
      (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
        (C c).space ⊆ convexHull ℝ (t : Set E) ∧
        P c = g '' (C c).space ∧ PolyhedralPLInCharts e g (C c).space ∧
        IsCompact (P c) ∧ IsConnected (P c)) ∧
      Pairwise (fun c d => Disjoint (C c).space (C d).space) ∧
      Pairwise (fun c d => Disjoint (P c) (P d)) ∧
      (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) ∧
      (⋃ c, P c) = (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i) ∧
      (∀ c x, x ∈ P c →
        connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x = P c) ∧
      ∀ c, ∃! i, P c ⊆ S i := by
  classical
  obtain ⟨M,hM,hMs⟩ := exists_original_sphere_family_complex_in_face he K hK hg hgi sS hS ht
  let : Finite M.vertices := (M.finite_vertices_of_finite_faces hM).to_subtype
  let γ := M.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let C : γ → SimplicialComplex ℝ E := M.edgeComponentComplex
  let P : γ → Set X := fun c => g '' (C c).space
  have hfinite (c : γ) : (C c).faces.Finite := hM.subset (M.edgeComponentComplex_le c)
  have hsource (c : γ) : (C c).space ⊆ convexHull ℝ (t : Set E) :=
    (SimplicialComplex.space_subset_of_le (M.edgeComponentComplex_le c)).trans
      (hMs.subset.trans inter_subset_left)
  have hCK (c : γ) : (C c).space ⊆ K.space :=
    (hsource c).trans (K.convexHull_subset_space ht)
  have hconn (c : γ) : IsConnected (C c).space :=
    (M.edgeComponentComplex_isPathConnected c).isConnected
  have hc (c : γ) : IsCompact (P c) :=
    ((C c).isCompact_space_of_finite (hfinite c)).image_of_continuousOn
      (hg.continuousOn.mono (hCK c))
  have hpconn (c : γ) : IsConnected (P c) :=
    (hconn c).image g (hg.continuousOn.mono (hCK c))
  have hpdis : Pairwise fun c d => Disjoint (P c) (P d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    have he : y = x := hgi (hCK d hy) (hCK c hx) heq
    exact disjoint_left.mp (M.pairwise_disjoint_edgeComponentComplex_space hcd)
      hx (he ▸ hy)
  have hcover : (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) :=
    M.iUnion_edgeComponentComplex_space.trans hMs
  have hpcover : (⋃ c, P c) = (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i) := by
    dsimp only [P]
    rw [←image_iUnion,hcover,image_inter_preimage]
  have hcomp (c : γ) (x : X) (hx : x ∈ P c) :
      connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x = P c := by
    let T := (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)
    have hsub (c : γ) : P c ⊆ T := (subset_iUnion P c).trans hpcover.subset
    have hxT := hsub c hx
    have hcc := isConnected_connectedComponentIn_iff.mpr hxT
    obtain ⟨d,hd,_⟩ := hcc.exists_unique_subset_finite_disjoint_closed
      P (fun c => (hc c).isClosed) hpdis
      ((connectedComponentIn_subset T x).trans hpcover.symm.subset)
    have hdc : d = c := by
      by_contra hn
      exact disjoint_left.mp (hpdis hn) (hd (mem_connectedComponentIn hxT)) hx
    subst d
    exact Subset.antisymm hd ((hpconn c).isPreconnected.subset_connectedComponentIn hx (hsub c))
  refine ⟨γ,inferInstance,C,P,?_,M.pairwise_disjoint_edgeComponentComplex_space,
    hpdis,hcover,hpcover,hcomp,?_⟩
  · intro c
    exact ⟨hfinite c,hconn c,hsource c,rfl,
      hg.restrict_finite (C c) (hfinite c) (hCK c),hc c,hpconn c⟩
  · intro c
    exact exists_unique_sphere_member_of_preconnected S sS hdis
      (hpconn c).nonempty (hpconn c).isPreconnected
      (fun x hx => (hpcover.subset (mem_iUnion.mpr ⟨c,hx⟩)).2)

end PoincareConjecture.M76
