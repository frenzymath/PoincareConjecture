import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarEndpointPL
import PoincareConjecture.Proofs.M76.Rigidity.LocalEmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.RelativeApproximation.ChartwiseRestriction
import Mathlib.RingTheory.Finiteness.Prod

set_option autoImplicit false

open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0

def hamiltonZeroAmbientMapInDomain (g : C(X0, X0)) : C(R0, R0) :=
  ⟨fun x => ⟨g x, hamiltonZeroDomain_eq_univ.symm.subset (mem_univ _)⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem hamiltonZeroAmbientMapInDomain_original (phi : C(H0, H0)) :
    hamiltonZeroAmbientMapInDomain (hamiltonZeroAmbientMap phi) =
      latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem chartwisePL_hamiltonZero_of_collar
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) {c : E × ℝ → X0}
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {delta r : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hwidth : 2 * r < delta)
    (hopen : IsOpen (c '' (L.space ×ˢ Ioo (-delta) delta)))
    (g : C(X0, X0))
    (hg : PolyhedralPLInCharts d (fun z => g (c z))
      (L.space ×ˢ Icc (-delta) delta))
    (hfixed : ∀ y : X0, y ∉ c '' (L.space ×ˢ Ioo (-(2 * r)) (2 * r)) →
      g y = hamiltonZeroAmbientMap phi y) :
    ChartwisePLMap e d (hamiltonZeroAmbientMapInDomain g) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let C := c '' (L.space ×ˢ Icc (-(2 * r)) (2 * r))
  let W := c '' (L.space ×ˢ Ioo (-delta) delta)
  have hsmall : L.space ×ˢ Icc (-(2 * r)) (2 * r) ⊆
      L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hC : IsClosed C :=
    ((L.isCompact_space_of_finite hL).prod isCompact_Icc).image_of_continuousOn
      (hc.continuousOn.mono hsmall) |>.isClosed
  have hCW : C ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩, rfl⟩
  let U : Set R0 := (Subtype.val : R0 → X0) ⁻¹' Cᶜ
  have hU : IsOpen U := hC.isOpen_compl.preimage continuous_subtype_val
  have hagree : EqOn (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi)
      (hamiltonZeroAmbientMapInDomain g) U := by
    intro y hy
    rw [← hamiltonZeroAmbientMapInDomain_original]
    apply Subtype.ext
    apply (hfixed y ?_).symm
    intro hystrip
    apply hy
    obtain ⟨z, hz, hzy⟩ := hystrip
    exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, hzy⟩
  have hexterior := hphi.congr_mono hU (subset_univ _) hagree
  apply chartwisePLMap_of_open_and_embedded_parameters (E := E × ℝ) e d
    (hamiltonZeroAmbientMapInDomain g) hexterior
  intro x hx
  have hxC : (x : X0) ∈ C := not_not.mp hx
  obtain ⟨K, hK, hKs⟩ := L.exists_finite_interval_product hL
    (show -delta < delta by linarith)
  have hsub : K.space ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    have hz' := hKs.subset hz
    exact ⟨hz'.1, by linarith [hz'.2.1], hz'.2.2.trans hdeltaOne⟩
  let q : E × ℝ → R0 := fun z =>
    ⟨c z, by rw [hamiltonZeroDomain_eq_univ]; trivial⟩
  have hqPL : PolyhedralPLInCharts e (fun z => (q z : X0)) K.space :=
    hc.restrict_finite K hK hsub
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  have hiK : Topology.IsEmbedding (fun z : K.space => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hsub)
  have hiq : Topology.IsEmbedding (fun z : K.space => q z) :=
    hiK.codRestrict R0 (fun _ => by rw [hamiltonZeroDomain_eq_univ]; trivial)
  have hWrange : (Subtype.val : R0 → X0) ⁻¹' W ⊆
      range (fun z : K.space => q z) := by
    rintro y ⟨z, hz, hzy⟩
    have hzK : z ∈ K.space := hKs.symm.subset ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
    exact ⟨⟨z, hzK⟩, Subtype.ext hzy⟩
  have hxW : x ∈ (Subtype.val : R0 → X0) ⁻¹' W := hCW hxC
  obtain ⟨z, hzx⟩ := hWrange hxW
  have hnhds : range (fun z : K.space => q z) ∈ 𝓝 x :=
    Filter.mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds hxW) hWrange
  have hgq : PolyhedralPLInCharts d
      (fun z => (hamiltonZeroAmbientMapInDomain g (q z) : X0)) K.space :=
    hg.restrict_finite K hK hKs.subset
  exact ⟨K, q, z, hK, hq, hiq, hzx, hnhds, hqPL, hgq⟩

end PoincareConjecture.M76
