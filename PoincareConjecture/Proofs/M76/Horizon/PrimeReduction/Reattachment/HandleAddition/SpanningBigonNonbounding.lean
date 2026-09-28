import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereSurgeryNonbounding








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem ChartwisePLSphere.exists_ball_of_ball_patch_replacement
    {X F ι : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R S S' U T : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (hR : IsCompact R)
    (u : ChartwisePLBall e U T) (hUR : U ⊆ R) (hS'R : S' ⊆ interior R)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : U ∩ S' = p '' d) (hdT : p '' d ⊆ T)
    (hS'out : (S' \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    (hboundary : S = (S' \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))
    (hfill : ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S')) :
    ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S) := by
  obtain ⟨B, hBR, ⟨b⟩⟩ := hfill
  have hBint : B ⊆ interior R := by
    intro x hx
    by_cases hi : x ∈ interior B
    · exact interior_mono hBR hi
    · apply hS'R
      rw [←b.frontier_eq]
      exact ⟨subset_closure hx, hi⟩
  have havoid : Disjoint (interior U) (frontier B) := by
    rw [b.frontier_eq]
    intro Z hZU hZS x hx
    have hxt : x ∈ T := hdT (hcontact.subset ⟨interior_subset (hZU hx), hZS hx⟩)
    have hxf : x ∈ frontier U := u.frontier_eq.symm ▸ hxt
    exact hxf.2 (hZU hx)
  rcases preconnected_interior_or_exterior_of_frontier_avoidance b.isCompact.isClosed
      u.isConnected_interior.isPreconnected havoid with hin | hout
  · have hUB : U ⊆ B := by
      rw [←u.closure_interior]
      exact closure_minimal (hin.trans interior_subset) b.isCompact.isClosed
    have hSB : S ⊆ B := by
      rw [hboundary]
      exact union_subset (sdiff_subset.trans b.boundary_subset)
        (sdiff_subset.trans (u.boundary_subset.trans hUB))
    exact s.exists_ball_of_subset_interior_ball he hR b hBint hSB
  · have hUout : U ⊆ (interior B)ᶜ := by
      rw [←u.closure_interior]
      exact closure_minimal (fun x hx hi => hout hx (interior_subset hi))
        isOpen_interior.isClosed_compl
    have hUB : U ∩ B = p '' d := by
      apply Subset.antisymm
      · intro x hx
        apply hcontact.subset
        refine ⟨hx.1, ?_⟩
        rw [←b.frontier_eq]
        exact ⟨subset_closure hx.2, hUout hx.1⟩
      · intro x hx
        obtain ⟨hxU, hxS'⟩ := hcontact.symm.subset hx
        exact ⟨hxU, b.boundary_subset hxS'⟩
    have hBU : B ∩ U = p '' d := inter_comm B U ▸ hUB
    obtain ⟨joined⟩ := b.union_of_original_disk_contact he hR u hBR hUR hd p hp hpi
      (hcontact.symm.subset.trans inter_subset_right) hdT hS'out hTout hBU
    rw [←hboundary] at joined
    exact ⟨B ∪ U, union_subset hBR hUR, ⟨joined⟩⟩

theorem ChartwisePLSphere.nonbounding_of_ball_patch_replacement
    {X F ι : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R S S' U T : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (hR : IsCompact R)
    (u : ChartwisePLBall e U T) (hUR : U ⊆ R) (hS'R : S' ⊆ interior R)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : U ∩ S' = p '' d) (hdT : p '' d ⊆ T)
    (hS'out : (S' \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    (hboundary : S = (S' \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))
    (hnonbounding : ¬∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S)) :
    ¬∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S') := by
  intro hfill
  exact hnonbounding (s.exists_ball_of_ball_patch_replacement he hR u hUR hS'R hd
    p hp hpi hcontact hdT hS'out hTout hboundary hfill)

end PoincareConjecture.M76

