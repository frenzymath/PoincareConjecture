import PoincareConjecture.Proofs.M47.PositiveHistoryGluing
import PoincareConjecture.Proofs.M47.PositiveHistoryInitialSlab
import PoincareConjecture.Proofs.M47.ComponentEstimateStrictHistory
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive




theorem exists_component_closed_ordinary_history
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin a : ℝ} (ha : a < 0)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U) :
    ∃ G : RicciFlow 3 U (Icc (origin + a) origin),
      ∀ (s : ℝ) (hs : s ∈ Icc a 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric (origin + s / 1)).inner (e.forward s hs x.val)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
              (G.metric (origin + s / 1)).inner x v w) ∧
        (G.connection (origin + s / 1)).scalarCurvature x =
          (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x.val) ∧
        (G.connection (origin + s / 1)).curvatureTensorNorm x =
          (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x.val) := by
  have haI : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  have h0I : 0 ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  have hstart : origin + a ∈ F.time_domain := by
    simpa only [div_one] using e.time_subset (mem_image_of_mem _ haI)
  have hterminal : origin ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using e.time_subset (mem_image_of_mem _ h0I)
  obtain ⟨c, hac, hcb, hfree⟩ := M44.exists_surgery_free_right_interval F hstart
    (show origin + a < origin by linarith)
  have hJ : Icc (origin + a) c ⊆ F.time_domain :=
    (Icc_subset_Icc le_rfl hcb.le).trans (F.time_domain_interval.out hstart hterminal)
  have ha' : origin + a / 1 ∈ Icc (origin + a) c := by
    simpa only [div_one] using (show origin + a ∈ Icc (origin + a) c from
      ⟨le_rfl, hac.le⟩)
  obtain ⟨F0, hm0⟩ := exists_component_slab_pullback U e hac hJ hfree a haI ha'
  obtain ⟨F1, hm1⟩ := M47.exists_component_strict_ordinary_history P ha U hne e
  have hmetric : ∀ t ∈ Ioc (origin + a) c, F0.metric t = F1.metric t := by
    intro t ht
    have hs : t - origin ∈ Ioc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht' : origin + (t - origin) / 1 ∈ Icc (origin + a) c := by
      simpa only [div_one, add_sub_cancel] using (Ioc_subset_Icc_self ht)
    have hinner : (F0.metric t).inner = (F1.metric t).inner := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      have h := (hm0 (t - origin) ⟨hs.1.le, hs.2⟩ ht' x v w).symm.trans
        ((hm1 (t - origin) hs x).1 v w)
      simpa only [div_one, add_sub_cancel] using h
    generalize F0.metric t = g₀ at hinner ⊢
    generalize F1.metric t = g₁ at hinner ⊢
    cases g₀
    cases g₁
    cases hinner
    rfl
  obtain ⟨G, hG0, hG1⟩ := exists_closed_flow_of_initial_overlap hac hcb.le F0 F1 hmetric
  have hm (s : ℝ) (hs : s ∈ Icc a 0) (x : U) (v w : TangentSpace (𝓡 3) x) :
      (F.metric (origin + s / 1)).inner (e.forward s hs x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
          (G.metric (origin + s / 1)).inner x v w := by
    by_cases hsa : s ≤ a
    · have hsaeq : s = a := le_antisymm hsa hs.1
      subst s
      rw [hG0 _ ha']
      exact hm0 a hs ha' x v w
    · have has : a < s := lt_of_not_ge hsa
      have ht : origin + s / 1 ∈ Ioc (origin + a) origin := by
        simp only [div_one]
        constructor <;> linarith [hs.2]
      rw [hG1 _ ht]
      exact (hm1 s ⟨has, hs.2⟩ x).1 v w
  refine ⟨G, ?_⟩
  intro s hs x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => e.forward s hs y.val) := by
    intro y
    exact ((e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val (n := ∞) y)
  refine ⟨hm s hs x, ?_, ?_⟩
  · exact (G.connection (origin + s / 1)).scalarCurvature_eq_of_local_isometry
      (F.connection (origin + s / 1)) isOpen_univ hf.contMDiffOn
      (fun y _hy v w => (hm s hs y v w).symm) (mem_univ x)
  · exact (G.connection (origin + s / 1)).curvatureTensorNorm_eq_of_local_isometry
      (F.connection (origin + s / 1)) isOpen_univ hf.contMDiffOn
      (fun y _hy v w => (hm s hs y v w).symm) (mem_univ x)

end PoincareConjecture.M47Positive
