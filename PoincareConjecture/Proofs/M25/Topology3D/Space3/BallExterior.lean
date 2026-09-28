import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D



theorem isPreconnected_compl_of_neighborhood
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {K W : Set X} (hK : IsClosed K) (hW : IsOpen W) (hKW : K ⊆ W)
    (houter : IsPreconnected (W \ K)) : IsPreconnected Kᶜ := by
  have step {u v : Set X} (hu : IsOpen u) (hv : IsOpen v)
      (hcover : Kᶜ ⊆ u ∪ v) (hdis : Kᶜ ∩ (u ∩ v) = ∅)
      (hside : W \ K ⊆ u) : Kᶜ ⊆ u ∨ Kᶜ ⊆ v := by
    have hwhole : (univ : Set X) ⊆ (u ∪ W) ∪ (v \ K) := by
      intro x _
      by_cases hx : x ∈ K
      · exact Or.inl (Or.inr (hKW hx))
      · rcases hcover hx with hu | hv
        · exact Or.inl (Or.inl hu)
        · exact Or.inr ⟨hv, hx⟩
    have hwholeDis : (univ : Set X) ∩ ((u ∪ W) ∩ (v \ K)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨_, hxu, hxv, hxK⟩
      have hxu' : x ∈ u := hxu.elim id (fun hxW => hside ⟨hxW, hxK⟩)
      have hbad : x ∈ Kᶜ ∩ (u ∩ v) := ⟨hxK, hxu', hxv⟩
      rwa [hdis] at hbad
    rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ
      (u ∪ W) (v \ K) (hu.union hW) (hv.sdiff hK) hwhole hwholeDis with h | h
    · exact Or.inl (fun x hx => (h (mem_univ x)).elim id (fun hxW => hside ⟨hxW, hx⟩))
    · exact Or.inr (fun x _ => (h (mem_univ x)).1)
  apply isPreconnected_iff_subset_of_disjoint.mpr
  intro u v hu hv hcover hdis
  have houterDis : (W \ K) ∩ (u ∩ v) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxuv⟩
    have hbad : x ∈ Kᶜ ∩ (u ∩ v) := ⟨hx.2, hxuv⟩
    rwa [hdis] at hbad
  rcases isPreconnected_iff_subset_of_disjoint.mp houter u v hu hv
    (fun _ hx => hcover hx.2) houterDis with h | h
  · exact step hu hv hcover hdis h
  · exact (step hv hu (by simpa only [union_comm] using hcover)
      (by simpa only [inter_comm v u] using hdis) h).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem isConnected_unitAnnulus (hdim : 1 < Module.rank ℝ E) {R : ℝ} (hR : 1 < R) :
    IsConnected (ball (0 : E) R \ closedBall 0 1) := by
  have himage : (fun p : E × ℝ => p.2 • p.1) ''
      (sphere 0 1 ×ˢ Ioo 1 R) = ball (0 : E) R \ closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨hq, ht⟩, rfl⟩
      have hn : ‖t • q‖ = t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans ht.1),
          mem_sphere_zero_iff_norm.mp hq, mul_one]
      simpa only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, hn] using
        And.intro ht.2 ht.1
    · intro hx
      rw [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le] at hx
      have hx0 : 0 < ‖x‖ := zero_lt_one.trans hx.2
      refine ⟨((‖x‖)⁻¹ • x, ‖x‖), ⟨?_, hx.2, hx.1⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hx0), inv_mul_cancel₀ hx0.ne']
      · dsimp
        rw [smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
  rw [← himage]
  exact ((isConnected_sphere hdim 0 zero_le_one).prod (isConnected_Ioo hR)).image
    (fun p : E × ℝ => p.2 • p.1) (continuous_snd.smul continuous_fst).continuousOn




theorem compactChart_exterior_connected [ProperSpace E]
    {X : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (e : OpenPartialHomeomorph E X) (hdim : 1 < Module.rank ℝ E)
    {R : ℝ} (hR : 1 < R) (hsource : ball 0 R ⊆ e.source) :
    IsConnected (e '' closedBall 0 1)ᶜ := by
  have hsmall : closedBall (0 : E) 1 ⊆ ball 0 R := closedBall_subset_ball hR
  have hK : IsCompact (e '' closedBall 0 1) :=
    (isCompact_closedBall (0 : E) 1).image_of_continuousOn
      (e.continuousOn.mono (hsmall.trans hsource))
  have hW : IsOpen (e '' ball 0 R) :=
    e.isOpen_image_of_subset_source isOpen_ball hsource
  have houter : IsConnected (e '' ball 0 R \ e '' closedBall 0 1) := by
    rw [← (e.injOn.mono hsource).image_sdiff_subset hsmall]
    exact (isConnected_unitAnnulus hdim hR).image e
      (e.continuousOn.mono (sdiff_subset.trans hsource))
  exact ⟨houter.nonempty.mono (fun _ hx => hx.2),
    isPreconnected_compl_of_neighborhood hK.isClosed hW (image_mono hsmall)
      houter.isPreconnected⟩

end PoincareConjecture.M25.Topology3D
