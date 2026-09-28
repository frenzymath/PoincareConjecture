import PoincareConjecture.Proofs.M76.Wall.OriginalNewFrontierModels
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.OriginalFrontierEssentialRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalSphereSimplyConnected
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation

set_option autoImplicit false
open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in

structure FrontierResidualModel {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (N F : Set X) where
  vertices : Finset N
  coordinates : X → (vertices → ℝ × V3)
  complex : SimplicialComplex ℝ (vertices → ℝ × V3)
  map : (vertices → ℝ × V3) → X
  count : ℕ
  pick : Fin count ↪ complex.vertexAbstractComplex.edgeGraph.ConnectedComponent
  components : Fin count → Set X
  residual : Fin count → ℕ
  coordinates_continuous : Continuous coordinates
  coordinates_injective : InjOn coordinates N
  coordinates_pl : ∀ i,
    LocallyPiecewiseAffineOn (coordinates ∘ (e i).symm) (e i).target
  finite : complex.faces.Finite
  dimension : ∀ t ∈ complex.faces, t.card ≤ 3
  pl : PolyhedralPLInCharts e map complex.space
  injective : InjOn map complex.space
  inverse : ∀ z ∈ complex.space, coordinates (map z) = z
  positive : 0 < count
  images : ∀ i, components i = map '' (complex.edgeComponentComplex (pick i)).space
  cover : (⋃ i, components i) = F
  disjoint : Pairwise fun i j => Disjoint (components i) (components j)
  component : ∀ i, IsCompact (components i) ∧ IsConnected (components i) ∧
    components i ⊆ F ∧ ∀ x ∈ components i, connectedComponentIn F x = components i
  euler : ∀ i, (complex.edgeComponentComplex (pick i)).surfaceEulerCount =
    2 - (residual i : ℤ)
  zero_sphere : ∀ i, residual i = 0 → Nonempty (ChartwisePLSphere e (components i))

def FrontierResidualModel.complexity {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}
    (M : FrontierResidualModel e N F) : ℕ :=
  ∑ i : Fin M.count, (M.residual i - 1)

open Classical in
theorem PLDomain.exists_frontier_residual_models
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty) :
    ∃ (s : Finset N) (phi : X → (s → ℝ × V3))
      (A : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X)
      (n : ℕ) (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (S : Fin n → Set X) (residual : Fin n → ℕ),
      Continuous phi ∧ InjOn phi N ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      A.faces.Finite ∧ (∀ t ∈ A.faces, t.card ≤ 3) ∧
      PolyhedralPLInCharts e g A.space ∧ InjOn g A.space ∧
      (∀ z ∈ A.space, phi (g z) = z) ∧ 0 < n ∧
      (∀ i, S i = g '' (A.edgeComponentComplex (pick i)).space) ∧
      (⋃ i, S i) = F ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        ∀ x ∈ S i, connectedComponentIn F x = S i) ∧
      (∀ i, (A.edgeComponentComplex (pick i)).surfaceEulerCount = 2 - (residual i : ℤ)) ∧
      ∀ i, residual i = 0 → Nonempty (ChartwisePLSphere e (S i)) := by
  obtain ⟨s, phi, K, A, H, g, HB, n, pick, S,
    hphi, hphiPL, hK, hAK, hA, _, _, _, hH, _, hg, hgPL, _, _, _, _,
    hpure, hcofaces, hlinks, hn, hS, hunion, hdisjoint, hcomponents, hsphere⟩ :=
    he.exists_new_frontier_component_models hN hNne hB hF hBF hfront hFne
  have hAS : A.space ⊆ K.space := SimplicialComplex.space_subset_of_le hAK
  have hphii : InjOn phi N := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hh : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hh)
  have hinverse (z) (hz : z ∈ A.space) : phi (g z) = z := by
    rw [hg ⟨z, hAS hz⟩, ← hH (H.symm ⟨z, hAS hz⟩), H.apply_symm_apply]
  have hdim (t) (ht : t ∈ A.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, htu, hu⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq hu
  have hr (i : Fin n) : ∃ r : ℕ,
      Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + r =
        Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    obtain ⟨_, _, _, _, _, _, L, _, _, hcount⟩ :=
      A.exists_edgeComponent_trees_with_residual_edges hA (pick i) hpure hcofaces hlinks
    exact ⟨L.card, hcount⟩
  choose residual hr using hr
  refine ⟨s, phi, A, fun z => g z, n, pick, S, residual, hphi, hphii, hphiPL,
    hA, hdim, hgPL.restrict_finite A hA hAS, hgi.mono hAS, hinverse, hn,
    hS, hunion, hdisjoint, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hcomponents i).1, (hcomponents i).2.1,
      (hcomponents i).2.2.1, (hcomponents i).2.2.2.1⟩
  · intro i
    exact (A.edgeComponentComplex (pick i)).surfaceEulerCount_eq_two_sub_residual (hr i)
  · intro i hz
    apply hsphere i
    simpa only [hz, Nat.add_zero] using hr i

theorem PLDomain.nonempty_frontier_residual_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty) :
    Nonempty (FrontierResidualModel e N F) := by
  classical
  obtain ⟨s, phi, A, g, n, pick, S, residual, hc, hi, hpl, hA, hdim,
    hg, hgi, hinv, hn, hS, hcover, hdis, hcomp, hcount, hsphere⟩ :=
    he.exists_frontier_residual_models hN hNne hB hF hBF hfront hFne
  exact ⟨⟨s, phi, A, g, n, pick, S, residual, hc, hi, hpl, hA, hdim,
    hg, hgi, hinv, hn, hS, hcover, hdis, hcomp, hcount, hsphere⟩⟩

end PoincareConjecture.M76
