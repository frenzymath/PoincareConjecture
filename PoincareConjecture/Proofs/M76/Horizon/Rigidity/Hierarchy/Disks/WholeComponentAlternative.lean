import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedCircleModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdPhaseCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdPhaseAlternative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ComponentFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.MarkedCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_compressed_third_marked_surface_chart
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroThirdCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {other}))) :
    let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}
    ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X0 V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source (frontier R)) ∨
        ∃ (ell height : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          height.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ height.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ height (T y)) ∧
          ∀ y ∈ T.source, y ∈ frontier R ↔ height (T y) = 0) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hcompact (t : C0) : IsCompact (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {t}) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset
      (heR.closed.inter (isClosed_singleton.preimage (hamiltonZeroThirdCircleMap psi).continuous))
      (subset_univ _)
  have hdis : Disjoint (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta})
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {other}) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hne (hx.2.symm.trans hy.2)
  exact marked_surface_charts_after_interior_change hN isClosed_frontier
    (hcompact other).isClosed hfront hdis hA.isClosed
    (disjoint_interior_frontier.mono_left hAR)
    (S := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {theta})
    (by
      intro x hx
      have hq : hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x := by
        simp only [hamiltonZeroThirdCircleMap_ambient, hfixed x hx]
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hq])
    (by
      intro x hx
      obtain ⟨T, hxT, hcompat, hkind⟩ := hreg.exists_marked_surface_chart x hx.1
      rcases hkind with ⟨_, _, _, _, hdis⟩ | ⟨ell, height, u, v, hu, hv, huv, hS, hB⟩
      · exact (disjoint_left.mp hdis hxT hx.2).elim
      · exact ⟨T, ell, height, u, v, hxT, hcompat, hu, hv, huv, hS, hB⟩)




theorem exists_hamiltonZero_third_whole_component_alternatives
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
    {R A : Set X0} (hI : IsPLIrreducible e R)
    (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroThirdCoordinateRegularity e R phi theta)
    {l r : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r) =
      ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {other})))
    {c alpha beta d a b : ℝ}
    (halpha : c < alpha) (hbeta : beta < c + p)
    (ha : d < a) (hb : b < d + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hinj : ∀ x : ↥(R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}), X0)) x)) :
    let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}
    ∃ (n : ℕ) (T : Fin n → Set X0),
      (⋃ i, T i) = S ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, IsCompact (T i) ∧ IsPathConnected (T i) ∧
        (∀ x ∈ T i, connectedComponentIn S x = T i) ∧
        ((∃ (H : D ≃ₜ T i) (j : V2 → X0), PolyhedralPLInCharts e j D ∧
          Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D R ∧
          (∀ z : D, j z = (H z : X0)) ∧ j '' D = T i ∧
          ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) ∨
        (Disjoint (T i) (frontier R) ∧ Nonempty (ChartwisePLSphere e (T i)) ∧
          ∃ B : Set X0, IsCompact B ∧ B ⊆ interior R ∧
            Nonempty (ChartwisePLBall e B (T i)))) := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}
  have hS : IsCompact S := isCompact_hamiltonZeroAmbient.of_isClosed_subset
    (hI.1.closed.inter (isClosed_singleton.preimage (hamiltonZeroThirdCircleMap psi).continuous))
    (subset_univ _)
  have hlocal := exists_hamiltonZero_compressed_third_marked_surface_chart
    e phi psi hI.1 hA hAR hfixed hne hreg hN hfront
  obtain ⟨s, F, K, _, g, hFc, hFi, _, hK, _, _, hKs, _,
    hgPL, hgi, hFg, hgS, _⟩ :=
    exists_original_marked_surface_finite_incidence
      e isCompact_hamiltonZeroAmbient hI.1 hS hlocal
  obtain ⟨n, T, hcover, hdis, hprops⟩ :=
    exists_whole_component_family_of_finite_model K hK F g hFc hFi hKs
      hgPL.continuousOn hgi hFg hgS
  refine ⟨n, T, hcover, hdis, ?_⟩
  intro i
  obtain ⟨hcompact, hconn, hcomponent, O, hO, hTO⟩ := hprops i
  have hTS : T i ⊆ S := by rw [← hcover]; exact subset_iUnion T i
  have hcharts := restrict_marked_surface_charts_to_open_piece e hO hTO hlocal
  have hTi (x : T i) : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(T i, X0)) x) := by
    have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(T i, X0)) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)).comp
          (ContinuousMap.inclusion hTS) := rfl
    rw [heq, FundamentalGroup.map_comp]
    exact (hinj ((ContinuousMap.inclusion hTS) x)).comp
      (FundamentalGroup.inclusion_injective_of_whole_component hTS hcomponent x)
  exact ⟨hcompact, hconn, hcomponent,
    exists_hamiltonZero_third_phase_disk_or_interior_ball e psi Fpsi hI hcompact
      (hTS.trans inter_subset_left) halpha hbeta ha hb hfirst hsecond theta
      (hTS.trans inter_subset_right) hconn hTi hcharts⟩

end PoincareConjecture.M76
