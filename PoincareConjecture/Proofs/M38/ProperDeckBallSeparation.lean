import PoincareConjecture.Proofs.M38.ProperCoverBallDescent
import PoincareConjecture.Proofs.M38.FiniteBallComplement
import PoincareConjecture.Proofs.M38.ClosedSetNesting
import PoincareConjecture.Proofs.Horizon.Topology.Covering.Quotient.Properness
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem compact_translate_eq_of_subset
    {X G : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
    [ProperlyDiscontinuousSMul G X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (g : G) (hsub : (g • ·) '' K ⊆ K) : (g • ·) '' K = K := by
  have hpow (n : ℕ) : (g ^ n • ·) '' K ⊆ K := by
    induction n with
    | zero => simpa only [pow_zero, one_smul, image_id'] using (Subset.rfl : K ⊆ K)
    | succ n ih =>
        rintro _ ⟨x, hx, rfl⟩
        change g ^ (n + 1) • x ∈ K
        rw [pow_succ', mul_smul]
        exact hsub ⟨g ^ n • x, ih (mem_image_of_mem _ hx), rfl⟩
  have hpowers : (Submonoid.powers g : Set G).Finite := by
    apply (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hK hK).subset
    intro a ha
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff a g).mp ha
    obtain ⟨x, hx⟩ := hne
    exact ⟨g ^ n • x, mem_image_of_mem _ hx, hpow n (mem_image_of_mem _ hx)⟩
  obtain ⟨n, hn, hgn⟩ := (finite_powers.mp hpowers).exists_pow_eq_one
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply Subset.antisymm hsub
  intro x hx
  refine ⟨g ^ m • x, hpow m (mem_image_of_mem _ hx), ?_⟩
  change g • (g ^ m • x) = x
  rw [← mul_smul, ← pow_succ', hgn, one_smul]

theorem surgeryBall_disjoint_translates_of_disjoint_frontiers
    {A : GeneralizedSliceCarrier.{u}}
    (hA : IsPreconnected (univ : Set A.carrier))
    (hnoncompact : ¬ IsCompact (univ : Set A.carrier))
    {G : Type*} [Group G] [MulAction G A.carrier]
    [ContinuousConstSMul G A.carrier] [ProperlyDiscontinuousSMul G A.carrier]
    (B : SurgeryBallEmbedding A)
    (hfront : ∀ g : G, g ≠ 1 →
      Disjoint (frontier B.closedBall) ((g • ·) '' frontier B.closedBall)) :
    ∀ g : G, g ≠ 1 → Disjoint B.closedBall ((g • ·) '' B.closedBall) := by
  have hcompact := surgeryBall_closedImage_compact B 1 (by norm_num)
  have hclosed : IsClosed B.closedBall := hcompact.isClosed
  have hconnected := surgeryBall_closedBall_connected B
  have hboundary := surgeryBall_frontier_connected B
  have hout : IsPreconnected B.closedBallᶜ := by
    simpa only [Set.sdiff_eq, univ_inter] using preconnected_diff_closed_of_local hA hclosed
      hconnected.nonempty (surgeryBall_image_open B)
      (surgeryBall_closedBall_subset_image B) (subset_univ _)
      (surgeryBall_outer_annulus_connected B).isPreconnected
  have hstrict (g : G) (hg : g ≠ 1) : ¬ (g • ·) '' B.closedBall ⊆ B.closedBall := by
    intro hsub
    have heq := compact_translate_eq_of_subset hcompact hconnected.nonempty g hsub
    have hf : (g • ·) '' frontier B.closedBall = frontier B.closedBall :=
      ((Homeomorph.smul g).image_frontier B.closedBall).trans (congrArg frontier heq)
    obtain ⟨x, hx⟩ := hboundary.nonempty
    exact disjoint_left.mp (hfront g hg) hx (hf.symm ▸ hx)
  intro g hg
  have hgc := hcompact.image (continuous_const_smul g)
  have hgf : frontier ((g • ·) '' B.closedBall) = (g • ·) '' frontier B.closedBall :=
    ((Homeomorph.smul g).image_frontier B.closedBall).symm
  have hfrontier : IsPreconnected (frontier ((g • ·) '' B.closedBall)) := by
    rw [hgf]
    exact hboundary.isPreconnected.image _ (continuous_const_smul g).continuousOn
  rcases closed_regions_nested_or_disjoint_or_cover hclosed hgc.isClosed
    hconnected.isPreconnected hout hfrontier (hgf.symm ▸ hfront g hg) with
    hsep | hsub | hsub | hcover
  · exact hsep
  · apply (hstrict g⁻¹ (inv_ne_one.mpr hg) ?_).elim
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hsub hx
    change g • y = x at hxy
    change g⁻¹ • x ∈ B.closedBall
    rw [← hxy, inv_smul_smul]
    exact hy
  · exact (hstrict g hg hsub).elim
  · exact (hnoncompact (hcover ▸ hcompact.union hgc)).elim

theorem exists_surgeryBall_descend_of_disjoint_lifted_frontiers
    {A Q : GeneralizedSliceCarrier.{u}}
    (hA : IsPreconnected (univ : Set A.carrier))
    (hnoncompact : ¬ IsCompact (univ : Set A.carrier))
    {G : Type*} [Group G] [MulAction G A.carrier]
    [ContinuousConstSMul G A.carrier] [ProperlyDiscontinuousSMul G A.carrier]
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hfibers : ∀ x y, q x = q y → ∃ g : G, y = g • x)
    (B : SurgeryBallEmbedding A)
    (hfront : ∀ g : G, g ≠ 1 →
      Disjoint (frontier B.closedBall) ((g • ·) '' frontier B.closedBall)) :
    ∃ D : SurgeryBallEmbedding Q,
      D.closedBall = q '' B.closedBall ∧ D.map 0 = q (B.map 0) ∧
        frontier D.closedBall = q '' frontier B.closedBall :=
  exists_surgeryBall_descend_proper_fibers q hq hfibers B
    (surgeryBall_disjoint_translates_of_disjoint_frontiers hA hnoncompact B hfront)

theorem exists_surgeryBall_descend_lifted_sphere
    {A Q : GeneralizedSliceCarrier.{u}}
    (hA : IsPreconnected (univ : Set A.carrier))
    (hnoncompact : ¬ IsCompact (univ : Set A.carrier))
    {G : Type*} [Group G] [MulAction G A.carrier]
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsQuotientCoveringMap q G)
    (f : UnitTwoSphere → Q.carrier) (hf : Function.Injective f)
    (L : UnitTwoSphere → A.carrier) (hlift : ∀ z, q (L z) = f z)
    (B : SurgeryBallEmbedding A) (hB : frontier B.closedBall = range L) :
    ∃ D : SurgeryBallEmbedding Q,
      D.closedBall = q '' B.closedBall ∧ D.map 0 = q (B.map 0) ∧
        frontier D.closedBall = range f := by
  let := hcover.toContinuousConstSMul
  let := hcover.properlyDiscontinuousSMul
  let := hcover.isCancelSMul
  have hfront (g : G) (hg : g ≠ 1) :
      Disjoint (frontier B.closedBall) ((g • ·) '' frontier B.closedBall) := by
    rw [hB]
    apply disjoint_left.mpr
    rintro _ ⟨z, rfl⟩ ⟨_, ⟨w, rfl⟩, hw⟩
    change g • L w = L z at hw
    have hwz : w = z := hf ((hlift w).symm.trans
      ((hcover.map_smul g).symm.trans ((congrArg q hw).trans (hlift z))))
    subst w
    exact hg (IsCancelSMul.right_cancel g 1 (L z) (hw.trans (one_smul G (L z)).symm))
  have hfibers (x y : A.carrier) (hxy : q x = q y) : ∃ g : G, y = g • x := by
    obtain ⟨g, hg⟩ := hcover.apply_eq_iff_mem_orbit.mp hxy.symm
    exact ⟨g, hg.symm⟩
  obtain ⟨D, hD, hc, hb⟩ := exists_surgeryBall_descend_of_disjoint_lifted_frontiers
    hA hnoncompact q hq hfibers B hfront
  refine ⟨D, hD, hc, hb.trans ?_⟩
  rw [hB, ← range_comp]
  exact congrArg range (funext hlift)

end PoincareConjecture.M38
