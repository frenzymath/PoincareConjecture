import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.Classification

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

theorem PairedSourceGeometry.exists_whole_phase_annuli
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (geometry : PairedSourceGeometry e phi a b)
    (noClosed : ∀ theta ∈ ({a, b} : Set ℝ), ∀ S : Set X,
      S.Nonempty → S ⊆ sourceSurface phi (theta : C) →
      (∀ x ∈ S, connectedComponentIn (sourceSurface phi (theta : C)) x = S) →
      Disjoint S (frontier R) → False) :
    ∀ theta ∈ ({a, b} : Set ℝ),
      ∃ (A : Ann ≃ₜ sourceSurface phi (theta : C)) (q : ℝ × ℝ → X),
        PolyhedralPLInCharts e q Ann ∧ (∀ x : Ann, (A x : X) = q x) ∧
        ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
          (sourceBoundaryCircle phi (theta : C) F0 (originalIntervalEndpoint side)
            (originalIntervalEndpoint_norm side)
            (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
              (by norm_num) (by norm_num) z) : X) := by
  intro theta htheta
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := ⟨(ha.trans hab).le, by linarith⟩
  have hdis : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    apply disjoint_left.mpr
    intro x hx hy
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp (hx.2.symm.trans hy.2))
  obtain ⟨other, hfront, hdisTheta⟩ : ∃ other : C,
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (theta : C) ∪ sourceSurface phi other) ∧
      Disjoint (sourceSurface phi (theta : C)) (sourceSurface phi other) := by
    rcases htheta with ht | ht
    · change theta = a at ht
      rw [ht]
      exact ⟨(b : C), geometry.frontiers (a, b) (Or.inl rfl), hdis⟩
    · change theta = b at ht
      rw [ht]
      exact ⟨(a : C), by simpa only [union_comm] using
        geometry.frontiers (a, b) (Or.inl rfl), hdis.symm⟩
  obtain ⟨S, A, q, n, T, hS, _, hq, hA, hmark, hcover, _, _, hT⟩ :=
    exists_compressed_source_phase_classification e d hd phi hphi F0
      (geometry.domains (a, b) (Or.inl rfl)) hfront hdisTheta
      (geometry.corners (a, b) (Or.inl rfl) theta htheta)
      (geometry.ambient_injective theta htheta)
  have hwhole : S = sourceSurface phi (theta : C) := by
    apply Subset.antisymm hS
    intro x hx
    rcases hcover.symm.subset hx with hxS | hxT
    · exact hxS
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxT
      obtain ⟨_, hconn, hsub, hcomponent, hrim, _⟩ := hT i
      exact (noClosed theta htheta (T i) hconn.nonempty hsub hcomponent hrim).elim
  exact ⟨A.trans (Homeomorph.setCongr hwhole), q, hq, hA, hmark⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
