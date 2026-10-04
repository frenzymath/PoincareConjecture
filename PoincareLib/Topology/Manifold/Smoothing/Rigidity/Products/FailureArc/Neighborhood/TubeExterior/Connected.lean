import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Domain
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.TwoPortComponentCarriers
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Topology.PLDomainLocalPathConnected
import Mathlib.Analysis.Normed.Module.Connected

/-! # Removing the actual spanning interval tube preserves connectedness -/

set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareMT.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem transverseSquare_eq_closedBall (r : ℝ) : transverseSquare r = closedBall (0 : P2) r := by
  ext x
  simp only [transverseSquare,mem_prod,mem_Icc,Metric.mem_closedBall,dist_eq_norm,
    sub_zero,Prod.norm_def,max_le_iff,Real.norm_eq_abs,abs_le]

theorem isConnected_lateral {r : ℝ} (hr : 0 < r) : IsConnected (lateral r) := by
  have hdim : 1 < Module.finrank ℝ P2 := by simp
  have hrank : 1 < Module.rank ℝ P2 := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  rw [lateral,transverseSquare_eq_closedBall,frontier_closedBall _ hr.ne']
  exact (isConnected_sphere hrank (0 : P2) hr.le).prod
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1))

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.isConnected_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) (hconn : IsConnected R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IsConnected (R \ U.map '' openTube r) := by
  let Q := R \ U.map '' openTube r
  let A := U.map '' closedTube r
  let L := U.map '' lateral r
  have hQ := OriginalIntervalTube.plDomain_exterior U hR he hr hr1
  let : LocallyPathConnectedSpace Q := hQ.locallyPathConnectedSpace
  have hAc : IsCompact A := (isCompact_closedTube r).image_of_continuousOn
    (U.pl.continuousOn.mono (closedTube_subset hr1.le))
  have hAconn : IsConnected A := by
    apply ((isFinitePLBallPair_closedTube hr).isConnected).image U.map
    exact U.pl.continuousOn.mono (closedTube_subset hr1.le)
  have hLconn : IsConnected L := (isConnected_lateral hr).image U.map
    (U.pl.continuousOn.mono ((lateral_subset r).trans (closedTube_subset hr1.le)))
  have hQA : Q ∩ A = L := by
    rw [inter_comm]
    exact OriginalIntervalTube.closedTube_inter_exterior U hr hr1.le
  have hcover : Q ∪ A = R := by
    rw [union_comm]
    exact OriginalIntervalTube.closedTube_union_exterior U hr1.le
  obtain ⟨a,ha⟩ := hLconn.nonempty
  have haQ : a ∈ Q := (hQA.symm.subset ha).1
  have hLQ : L ⊆ Q := hQA.symm.subset.trans inter_subset_left
  have hLC : L ⊆ connectedComponentIn Q a :=
    hLconn.isPreconnected.subset_connectedComponentIn ha hLQ
  have hmerged := Topology.componentIn_closed_two_port_attachment hQ.closed hAc.isClosed
    hAconn (hQA.symm.subset ha) (hQA.symm.subset ha)
    (fun x hx => Or.inl (hLC (hQA.subset hx)))
  rw [union_self] at hmerged
  have hwhole : connectedComponentIn (Q ∪ A) a = R := by
    rw [hcover]
    exact hconn.isPreconnected.connectedComponentIn (sdiff_subset haQ)
  have hQC : Q = connectedComponentIn Q a := by
    apply Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro x hx
    have hxR : x ∈ R := sdiff_subset hx
    rw [← hwhole,hmerged] at hxR
    rcases hxR with hxC|hxA
    · exact hxC
    · exact hLC (hQA.subset ⟨hx,hxA⟩)
  change IsConnected Q
  rw [hQC]
  exact ⟨⟨a,mem_connectedComponentIn haQ⟩,isPreconnected_connectedComponentIn⟩

end PoincareMT.M76.Dehn.Annuli.TubeExterior
