import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.BoundaryPhaseCover










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem exists_sourcePhase_finite_chart_cover
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi)) :
    ∃ (s : Finset R) (i : s → α) (K : s → SimplicialComplex ℝ V3)
      (w : s → V3 → ℝ),
      (∀ j, (K j).faces.Finite) ∧ (∀ j, (K j).space ⊆ (e (i j)).target) ∧
      (∀ j, (K j).AffineOnFaces (w j)) ∧
      (∀ j (y : R), (y : X) ∈ (e (i j)).source → e (i j) y ∈ (K j).space →
        sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
          (w j (e (i j) y) : C)) ∧
      ∀ x ∈ R, ∃ j, x ∈ (e (i j)).source ∧ e (i j) x ∈ interior (K j).space := by
  classical
  have hlocal (x : R) : ∃ (i : α) (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      K.faces.Finite ∧ (x : X) ∈ (e i).source ∧ e i x ∈ interior K.space ∧
      K.space ⊆ (e i).target ∧ K.AffineOnFaces w ∧
      ∀ (y : R), (y : X) ∈ (e i).source → e i y ∈ K.space →
        sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
          (w (e i y) : C) := by
    obtain ⟨i, hxi⟩ := hphi.source_domain.cover x
    obtain ⟨K, w, hK, hxK, hKt, hw, hlift⟩ :=
      exists_sourcePhase_lift_in_compatible_chart e d hd phi hphi x (e i)
        (fun j => hphi.source_domain.compatible j i) hxi
    exact ⟨i, K, w, hK, hxi, hxK, hKt, hw, hlift⟩
  choose i K w hK hxi hxK hKt hw hlift using hlocal
  let U : R → Set X := fun x => (e (i x)).source ∩ e (i x) ⁻¹' interior (K x).space
  have hU (x : R) : IsOpen (U x) :=
    (e (i x)).continuousOn.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  obtain ⟨s, hs⟩ := (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L).elim_finite_subcover
    U hU (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxi ⟨x, hx⟩, hxK ⟨x, hx⟩⟩)
  refine ⟨s, (fun j => i j.val), (fun j => K j.val), (fun j => w j.val),
    (fun j => hK j.val), (fun j => hKt j.val), (fun j => hw j.val),
    (fun j => hlift j.val), ?_⟩
  intro x hx
  obtain ⟨y, hys, hy⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨⟨y, hys⟩, hy⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
