import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyCoordinates
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))


noncomputable def sourcePhase (phi : C(H, H)) : C(H, C) :=
  ⟨fun x => (hamiltonOneHierarchyCoordinates (phi x)).2,
    continuous_snd.comp (hamiltonOneHierarchyCoordinates.continuous.comp phi.continuous)⟩

theorem sourcePhase_eq_on_boundary (phi : C(H, H))
    (F : (ContinuousMap.id H).HomotopyRel phi B) (x : H) (hx : x ∈ B) :
    sourcePhase phi x = (hamiltonOneHierarchyCoordinates x).2 := by
  have hfix : phi x = x := (F.apply_one x).symm.trans (F.eq_fst 1 hx)
  change (hamiltonOneHierarchyCoordinates (phi x)).2 = _
  rw [hfix]


theorem sourcePhase_boundary_surjective (phi : C(H, H))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : closedBall (0 : V1) 1) (hb : ‖(b : V1)‖ = 1) (c : C) :
    ∃ x ∈ B, x.1 = b ∧ sourcePhase phi x = c := by
  let x := hamiltonOneHierarchyCoordinates.symm ((b, 0), c)
  have hx : x ∈ B := ⟨hb, mem_univ _⟩
  refine ⟨x, hx, rfl, ?_⟩
  rw [sourcePhase_eq_on_boundary phi F x hx]
  exact congrArg Prod.snd (hamiltonOneHierarchyCoordinates.apply_symm_apply ((b, 0), c))




theorem exists_sourcePhase_finite_lift
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (x : R) :
    ∃ (i : α) (K : SimplicialComplex ℝ V3) (V : Set R) (w : V3 → ℝ),
      K.faces.Finite ∧ IsOpen V ∧ x ∈ V ∧
      MapsTo (Subtype.val : R → X) V (e i).source ∧
      ((e i) ∘ (Subtype.val : R → X)) '' V ⊆ K.space ∧
      K.space ⊆ (e i).target ∧ MapsTo (e i).symm K.space R ∧
      K.AffineOnFaces w ∧
      ∀ (z : V3) (_hz : z ∈ K.space) (hy : (e i).symm z ∈ R),
        sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L
          ⟨(e i).symm z, hy⟩) = (w z : C) := by
  obtain ⟨i, j, K, V, f, hK, hV, hxV, _, hVi, hVK, hKt, hKR, hf, hformula⟩ :=
    hphi.coordinates x (mem_univ x)
  obtain ⟨a, ha⟩ := hd.inverse_formula j
  let ell : V3 →ᴬ[ℝ] ℝ :=
    ((ContinuousLinearMap.proj (1 : Fin 2) : V2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ V1 V2)).toContinuousAffineMap.comp
        a.toContinuousAffineMap
  obtain ⟨J, hJ, hJK, hw⟩ := hf.postcomp ell
  refine ⟨i, J, V, ell ∘ f, hJ, hV, hxV, hVi, ?_, ?_, ?_, hw, ?_⟩
  · exact hVK.trans hJK.symm.subset
  · exact hJK.subset.trans hKt
  · intro z hz
    obtain ⟨y, _, hy⟩ := hKR (hJK.subset hz)
    exact hy ▸ y.property
  · intro z hz hy
    let y : R := ⟨(e i).symm z, hy⟩
    have hzt := hKt (hJK.subset hz)
    have hiy : e i (y : X) = z := (e i).right_inv hzt
    obtain ⟨hys, heq⟩ := hformula y ((e i).map_target hzt)
      (by rw [hiy]; exact hJK.subset hz)
    rw [hiy] at heq
    have hft : f z ∈ (d j).target := heq.symm ▸ (d j).map_source hys
    have hactual : (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi y : X) =
        ((a (f z)).1, QuotientAddGroup.mk (a (f z)).2) := by
      calc
        (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi y : X) =
            (d j).symm (d j (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi y)) :=
          ((d j).left_inv hys).symm
        _ = (d j).symm (f z) := congrArg (d j).symm heq.symm
        _ = ((a (f z)).1, QuotientAddGroup.mk (a (f z)).2) := ha (f z) hft
    change hamiltonLowerLatticePiEquiv (Fin 2)
      (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi y : X).2 1 = (ell (f z) : C)
    rw [hactual]
    rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
