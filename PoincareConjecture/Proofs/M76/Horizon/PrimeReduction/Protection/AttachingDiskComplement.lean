import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachingDiskTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers







set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.isConnected_attaching_disk_complement
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (hpos : 0 < Fintype.card ι) (hk : 1 < Fintype.card κ) :
    IsConnected ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      Metric.ball (0 : κ → ℝ) (3/2))ᶜ := by
  classical
  let q : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  let A := (q '' Metric.ball (0 : κ → ℝ) (3/2))ᶜ
  let B := q '' closedBall (0 : κ → ℝ) (3/2)
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hqo : IsOpenMap q :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph.isOpenMap
  have hA : IsClosed A := (hqo _ isOpen_ball).isClosed_compl
  have hB : IsClosed B := ((isCompact_closedBall _ _).image hq).isClosed
  have hBc : IsConnected B := ((convex_closedBall (0 : κ → ℝ) (3/2)).isConnected
    ⟨0, mem_closedBall_self (by norm_num)⟩).image q hq.continuousOn
  have hAB : A ∩ B = q '' sphere (0 : κ → ℝ) (3/2) := by
    ext x
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      rw [mem_sphere]
      exact le_antisymm hy (le_of_not_gt (fun h => hx ⟨y,h,rfl⟩))
    · rintro ⟨y,hy,rfl⟩
      refine ⟨?_,⟨y,sphere_subset_closedBall hy,rfl⟩⟩
      rintro ⟨z,hz,hzy⟩
      have hzy' := b.quotient_injOn_attaching_disk hpos
        (ball_subset_closedBall hz) (sphere_subset_closedBall hy) hzy
      subst z
      have hy' : dist y 0 = 3/2 := hy
      have hz' : dist y 0 < 3/2 := hz
      linarith
  have hABc : IsConnected (A ∩ B) := by
    rw [hAB]
    exact (isConnected_sphere (by simpa using hk) (0 : κ → ℝ)
      (by norm_num : (0 : ℝ) ≤ 3/2)).image q hq.continuousOn
  have hu : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ q '' Metric.ball (0 : κ → ℝ) (3/2)
    · exact Or.inr (image_mono ball_subset_closedBall hx)
    · exact Or.inl hx
  let : ConnectedSpace ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    QuotientAddGroup.mk_surjective.connectedSpace QuotientAddGroup.continuous_mk
  obtain ⟨x,hxA,hxB⟩ := hABc.nonempty
  have hcomp : A = connectedComponentIn A x := by
    apply Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro y hy
    apply (Topology.mem_componentIn_closed_attachment_iff hA hB hBc hABc hxA hy).mp
    rw [hu, isPreconnected_univ.connectedComponentIn (mem_univ x)]
    exact mem_univ y
  change IsConnected A
  rw [hcomp]
  exact ⟨⟨x,mem_connectedComponentIn hxA⟩,isPreconnected_connectedComponentIn⟩

end PoincareConjecture.M76
