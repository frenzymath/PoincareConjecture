import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.PolyhedralPLSelection
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetPhaseRetractionPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalHandleHomotopy











set_option autoImplicit false

open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0




theorem chartwisePL_hamiltonZero_of_phase_selection {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (theta : ℝ) (g : C(X0, X0))
    (hselect : ∀ x : X0, g x = hamiltonZeroAmbientMap phi x ∨
      g x = hamiltonZeroTargetPhaseRetraction theta (hamiltonZeroAmbientMap phi x)) :
    ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain g) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hempty : ChartwisePLOn e d (hamiltonZeroAmbientMapInDomain g) ∅ :=
    hphi.congr_mono isOpen_empty (empty_subset _) (fun _ hx => hx.elim)
  apply chartwisePLMap_of_open_and_embedded_parameters (E := V3) e d
    (hamiltonZeroAmbientMapInDomain g) hempty
  intro x _
  obtain ⟨i, j, K, V, f, hK, hV, hxV, _, hVi, hVK, hKt, _, _, _⟩ :=
    hphi.coordinates x (mem_univ x)
  let q : V3 → R0 := fun z =>
    ⟨(e i).symm z, hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _)⟩
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      ((e i).symm.continuousOn.mono hKt)
  have hi : Topology.IsEmbedding (fun z : K.space => (e i).symm z) :=
    (e i).symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion hKt)
  have hiq : Topology.IsEmbedding (fun z : K.space => q z) :=
    hi.codRestrict R0 (fun _ => hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _))
  have hxK : e i x ∈ K.space := hVK ⟨x, hxV, rfl⟩
  let z : K.space := ⟨e i x, hxK⟩
  have hqz : q z = x := Subtype.ext ((e i).left_inv (hVi hxV))
  have hVrange : V ⊆ range (fun z : K.space => q z) := by
    intro y hy
    exact ⟨⟨e i y, hVK ⟨y, hy, rfl⟩⟩, Subtype.ext ((e i).left_inv (hVi hy))⟩
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X0)) K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK) i hKt
  have h₀ := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hqPL
  have h₁ := hd.polyhedralPL_hamiltonZeroTargetPhaseRetraction theta h₀
  have hg : PolyhedralPLInCharts d (fun z => g (q z)) K.space :=
    h₀.continuous_selection hd.domain.cover hd.domain.compatible K hK h₁
      (g.continuous.comp_continuousOn hqPL.continuousOn)
      (fun z _ => hselect (q z))
  exact ⟨K, q, z, hK, hq, hiq, hqz,
    Filter.mem_of_superset (hV.mem_nhds hxV) hVrange, hqPL, hg⟩

end PoincareConjecture.M76
