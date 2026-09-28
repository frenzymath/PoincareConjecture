import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Domains

set_option autoImplicit false
open Set Metric Bornology

namespace PoincareConjecture.M76

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "D" => closedBall (0 : Plane) 1
local notation "Q" => sphere (0 : Plane) 1

theorem planar_surjective_of_eqOn_compl_compact
    {f : Plane → Plane} (hf : Continuous f) {K : Set Plane}
    (hK : IsCompact K) (hfix : EqOn f id Kᶜ) : Function.Surjective f := by
  intro a
  let g : Plane → Plane := fun x => x - f x + a
  have hg : Continuous g := (continuous_id.sub hf).add continuous_const
  have hC : IsCompact (g '' K ∪ {a}) := (hK.image hg).union (isCompact_singleton)
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall (0 : Plane)
  have hgr : ∀ x, g x ∈ closedBall (0 : Plane) (max r 0 + 1) := by
    intro x
    apply closedBall_subset_closedBall (by linarith [le_max_left r 0]) (hr ?_)
    by_cases hx : x ∈ K
    · exact Or.inl ⟨x, hx, rfl⟩
    · right
      simpa [g, hfix hx]
  let F : C(closedBall (0 : Plane) (max r 0 + 1), closedBall (0 : Plane) (max r 0 + 1)) :=
    ⟨fun x => ⟨g x, hgr x⟩, (hg.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := Poincare.Topology.Plane.Jordan.Brouwer.brouwerFPT
    (closedBall (0 : Plane) (max r 0 + 1)) (convex_closedBall _ _)
    (isCompact_closedBall _ _) ⟨0, mem_closedBall_self (by positivity)⟩ F
  refine ⟨x, ?_⟩
  have hh : (x : Plane) - f x + a = x := congrArg Subtype.val hx
  exact (sub_eq_zero.mp (by
    calc f x - a = (x : Plane) - ((x : Plane) - f x + a) := by abel
         _ = 0 := by rw [hh]; abel))

theorem bounded_jordan_side_subset_filling
    {Z : Type} [TopologicalSpace Z] [TietzeExtension.{0, 0} Z]
    (g : C(Z, Plane))
    (r : C(Q, Plane)) (hr : Function.Injective r)
    (inc : C(Q, Z)) (hboundary : ∀ z, g (inc z) = r z)
    {U : Set Plane} (hUb : IsBounded U)
    (hfront : frontier U = range r) : U ⊆ range g := by
  classical
  let H : Q ≃ₜ range r := (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective r hr) (r.continuous.subtype_mk _))
  let b : C(range r, Z) := inc.comp ⟨H.symm, H.symm.continuous⟩
  obtain ⟨e, he⟩ := ContinuousMap.exists_restrict_eq
    (isCompact_range r.continuous).isClosed b
  let rho : Plane → Plane := fun x => g (e x)
  have hrho : Continuous rho := g.continuous.comp e.continuous
  have hrhofix : EqOn rho id (frontier U) := by
    intro x hx
    have hxR : x ∈ range r := hfront ▸ hx
    have heq : e x = b ⟨x, hxR⟩ := DFunLike.congr_fun he ⟨x, hxR⟩
    change g (e x) = x
    rw [heq]
    change g (inc (H.symm ⟨x, hxR⟩)) = x
    exact (hboundary (H.symm ⟨x, hxR⟩)).trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨x, hxR⟩))
  let f : Plane → Plane := U.piecewise rho id
  have hf : Continuous f := Continuous.piecewise hrhofix hrho continuous_id
  have hfix : EqOn f id (closure U)ᶜ := by
    intro x hx
    exact piecewise_eq_of_notMem _ _ _ (fun h => hx (subset_closure h))
  have hsurj := planar_surjective_of_eqOn_compl_compact hf hUb.isCompact_closure hfix
  intro x hx
  obtain ⟨y, hy⟩ := hsurj x
  by_cases hyU : y ∈ U
  · exact ⟨e y, (piecewise_eq_of_mem U rho id hyU).symm.trans hy⟩
  · have hyx : y = x := (piecewise_eq_of_notMem U rho id hyU).symm.trans hy
    exact False.elim (hyU (hyx ▸ hx))

end PoincareConjecture.M76

