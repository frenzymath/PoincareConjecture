import PoincareConjecture.Proofs.M76.Mathlib.ConnectedBallExterior
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Bornology.IsBounded.exists_unique_unbounded_complement_component
    {A : Set E} (hA : Bornology.IsBounded A) (hdim : 1 < Module.rank ℝ E) :
    ∃ x ∈ Aᶜ, ¬ Bornology.IsBounded (connectedComponentIn Aᶜ x) ∧
      ∀ y, connectedComponentIn Aᶜ y ≠ connectedComponentIn Aᶜ x →
        Bornology.IsBounded (connectedComponentIn Aᶜ y) := by
  let : Nontrivial E := rank_pos_iff_nontrivial.mp (lt_trans zero_lt_one hdim)
  obtain ⟨r, hAr⟩ := hA.subset_closedBall (0 : E)
  have hext := isConnected_compl_closedBall_zero (E := E) hdim r
  obtain ⟨x, hx⟩ := hext.nonempty
  have hsub : (closedBall (0 : E) r)ᶜ ⊆ Aᶜ := compl_subset_compl.mpr hAr
  have hcomp := hext.isPreconnected.subset_connectedComponentIn hx hsub
  have hunbounded : ¬ Bornology.IsBounded (closedBall (0 : E) r)ᶜ := by
    intro h
    apply NormedSpace.unbounded_univ ℝ E
    simpa only [union_compl_self] using (isBounded_closedBall (x := (0 : E)) (r := r)).union h
  refine ⟨x, hsub hx, fun h => hunbounded (h.subset hcomp), ?_⟩
  intro y hne
  apply (isBounded_closedBall (x := (0 : E)) (r := r)).subset
  intro q hq
  by_contra hqr
  have hqx := hcomp hqr
  exact hne ((connectedComponentIn_eq hq).trans (connectedComponentIn_eq hqx).symm)
