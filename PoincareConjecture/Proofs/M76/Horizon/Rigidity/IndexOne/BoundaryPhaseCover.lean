import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhaseCharts
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_sourcePhase_boundary_cover
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi)) :
    ∃ (s : Finset (frontier R)) (G : s → OpenPartialHomeomorph X V3)
      (psi : s → V3 →ᴬ[ℝ] ℝ) (u : s → V3)
      (K : s → SimplicialComplex ℝ V3) (w : s → V3 → ℝ),
      (∀ i, (psi i).contLinear (u i) = 1) ∧
      (∀ i, (K i).faces.Finite) ∧
      (∀ i, (K i).space ⊆ (G i).target) ∧
      (∀ i, (K i).AffineOnFaces (w i)) ∧
      (∀ i, (K i).RespectsAffineHyperplane (psi i).toAffineMap) ∧
      (∀ i j, (e j).symm.trans (G i) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ i y, y ∈ (G i).source → (y ∈ R ↔ 0 ≤ psi i (G i y))) ∧
      (∀ i (y : R), (y : X) ∈ (G i).source → G i y ∈ (K i).space →
        sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
          (w i (G i y) : C)) ∧
      ∀ x ∈ frontier R, ∃ i, x ∈ (G i).source ∧ G i x ∈ interior (K i).space := by
  classical
  have hlocal (x : frontier R) :
      ∃ (G : OpenPartialHomeomorph X V3) (psi : V3 →ᴬ[ℝ] ℝ) (u : V3)
        (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
        psi.contLinear u = 1 ∧ (x : X) ∈ G.source ∧ G x ∈ interior K.space ∧
        K.faces.Finite ∧ K.space ⊆ G.target ∧ K.AffineOnFaces w ∧
        K.RespectsAffineHyperplane psi.toAffineMap ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ R ↔ 0 ≤ psi (G y)) ∧
        ∀ (y : R), (y : X) ∈ G.source → G y ∈ K.space →
          sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
            (w (G y) : C) := by
    obtain ⟨psi, u, G, hu, hxG, _, hG, hGR⟩ :=
      hphi.source_domain.halfspace x x.property
    let xR : R := ⟨x, hphi.source_domain.closed.frontier_subset x.property⟩
    obtain ⟨K, w, hK, hxK, hKt, hw, hlift⟩ :=
      exists_sourcePhase_lift_in_compatible_chart e d hd phi hphi xR G hG hxG
    let N := hK.toFinset.sup Finset.card
    have hN (s : Finset V3) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
      (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
    obtain ⟨J, hJ, hJK, _, hJpsi⟩ :=
      K.exists_subdivision_respectsAffineHyperplanes hK hN {psi.toAffineMap}
    refine ⟨G, psi, u, J, w, hu, hxG, ?_, hJ, ?_, hJK.affineOnFaces hw,
      hJpsi psi.toAffineMap (Finset.mem_singleton_self _), hG, hGR, ?_⟩
    · simpa only [hJK.space_eq] using hxK
    · rw [hJK.space_eq]; exact hKt
    · intro y hyG hyJ
      exact hlift y hyG (hJK.space_eq.subset hyJ)
  choose G psi u K w hu hxG hxK hK hKt hw hKpsi hG hGR hlift using hlocal
  let U : frontier R → Set X := fun x => (G x).source ∩ G x ⁻¹' interior (K x).space
  have hU (x : frontier R) : IsOpen (U x) :=
    (G x).continuousOn.isOpen_inter_preimage (G x).open_source isOpen_interior
  have hfront : IsCompact (frontier R) :=
    (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L).of_isClosed_subset
      isClosed_frontier hphi.source_domain.closed.frontier_subset
  obtain ⟨s, hs⟩ := hfront.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxG ⟨x, hx⟩, hxK ⟨x, hx⟩⟩)
  refine ⟨s, (fun i => G i.val), (fun i => psi i.val), (fun i => u i.val),
    (fun i => K i.val), (fun i => w i.val), (fun i => hu i.val),
    (fun i => hK i.val), (fun i => hKt i.val), (fun i => hw i.val),
    (fun i => hKpsi i.val), (fun i => hG i.val), (fun i => hGR i.val),
    (fun i => hlift i.val), ?_⟩
  intro x hx
  obtain ⟨y, hys, hy⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨⟨y, hys⟩, hy⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
