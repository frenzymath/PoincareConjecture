import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.TargetTranslation
import PoincareConjecture.Proofs.M76.Rigidity.LocalEmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.RelativeApproximation.ChartwiseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart










set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L


noncomputable def translatedMap (phi : C(H, H)) (w : C(X, ℝ)) : C(H, H) where
  toFun x := handleTranslation
    (w ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X), phi x)
  continuous_toFun := by fun_prop

theorem translatedMap_domain (phi : C(H, H)) (w : C(X, ℝ)) (x : R) :
    (latticeHandleMapInDomain (Fin 1) (Fin 2) L (translatedMap phi w) x : X) =
      targetTranslation (w x, (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi x : X)) := by
  change ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
    (handleTranslation
      (w ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) : X),
       phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x))) : X) = _
  rw [Homeomorph.symm_apply_apply, handleTranslation_domain]
  rfl

theorem exists_relative_source_parameter
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (f : C(R, R))
    (hf : ChartwisePLMap e d f) (x : R) :
    ∃ (K : SimplicialComplex ℝ V3) (q : V3 → R) (z : K.space),
      K.faces.Finite ∧ ContinuousOn q K.space ∧
      Topology.IsEmbedding (fun u : K.space => q u) ∧ q z = x ∧
      range (fun u : K.space => q u) ∈ 𝓝 x ∧
      PolyhedralPLInCharts e (fun u => (q u : X)) K.space := by
  classical
  obtain ⟨i, _, K, V, _, hK, hV, hxV, _, hVi, hVK, hKt, hKR, _, _⟩ :=
    hf.coordinates x (mem_univ x)
  have hinR (u : V3) (hu : u ∈ K.space) : (e i).symm u ∈ R := by
    obtain ⟨y, _, hy⟩ := hKR hu
    exact hy ▸ y.property
  let q : V3 → R := fun u => if hu : u ∈ K.space then ⟨(e i).symm u, hinR u hu⟩ else x
  have hqval (u : V3) (hu : u ∈ K.space) : (q u : X) = (e i).symm u := by simp [q, hu]
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (((e i).symm.continuousOn.mono hKt).congr hqval)
  have hi : Topology.IsEmbedding (fun u : K.space => (q u : X)) := by
    have heq : (fun u : K.space => (q u : X)) = fun u : K.space => (e i).symm u :=
      funext (fun u => hqval u u.property)
    rw [heq]
    exact (e i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun u : K.space => q u) :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hi
  have hxK : e i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  let z : K.space := ⟨e i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((hqval _ hxK).trans ((e i).left_inv (hVi hxV)))
  have hVrange : V ⊆ range (fun u : K.space => q u) := by
    intro y hy
    have hyK := hVK ⟨y, hy, rfl⟩
    exact ⟨⟨e i y, hyK⟩, Subtype.ext ((hqval _ hyK).trans ((e i).left_inv (hVi hy)))⟩
  have hqPL : PolyhedralPLInCharts e (fun u => (q u : X)) K.space := by
    apply (polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK)
      i hKt).congr
    intro u hu
    exact (hqval u hu).symm
  exact ⟨K, q, z, hK, hq, hiq, hqz, Filter.mem_of_superset (hV.mem_nhds hxV) hVrange, hqPL⟩



theorem chartwisePL_translatedMap
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (w : C(X, ℝ))
    (hw : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target) :
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L (translatedMap phi w)) := by
  have hempty : ChartwisePLOn e d
      (latticeHandleMapInDomain (Fin 1) (Fin 2) L (translatedMap phi w)) ∅ :=
    hphi.congr_mono isOpen_empty (empty_subset _) (fun _ hx => hx.elim)
  apply chartwisePLMap_of_open_and_embedded_parameters (E := V3) e d _ hempty
  intro x _
  obtain ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL⟩ :=
    exists_relative_source_parameter e d _ hphi x
  have hY := hphi.polyhedralPLInCharts_comp K hK q hq hqPL (fun _ _ => mem_univ _)
  have hwq := hqPL.finitePiecewiseAffineOn_comp K hK hw
  have hg := polyhedralPL_targetTranslation hd hY hwq
  refine ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL, hg.congr ?_⟩
  intro u _
  exact (translatedMap_domain phi w (q u)).symm

end PoincareConjecture.M76.HamiltonIntervalTorus
