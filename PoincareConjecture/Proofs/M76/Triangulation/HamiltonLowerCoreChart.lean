import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerLatticeImmersion
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardAtlasExistence










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)
local notation "V3" => (Fin 3 → ℝ)





theorem HamiltonLowerLatticeImmersion.exists_original_doubled_core_chart
    (I : HamiltonLowerLatticeImmersion κ)
    (h : OpenPartialHomeomorph V V3) {b : ℝ} (hb : 1 < b)
    (hsource : ball (0 : ι → ℝ) b ×ˢ I.compactCarrier ⊆ h.source) :
    ∃ e : OpenPartialHomeomorph W V3,
      e.source ⊆ ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ ∧
      EqOn e (fun z : W => h (z.1, I.map z.2)) e.source ∧
      ∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
        (x.1, QuotientAddGroup.mk x.2) ∈ e.source ∧
          e (x.1, QuotientAddGroup.mk x.2) = h x := by
  classical
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : DiscreteTopology (hamiltonLowerPeriodLattice κ) := inferInstance
  let π : V → W := fun x => (x.1, QuotientAddGroup.mk x.2)
  let U : Set V := ball (0 : ι → ℝ) b ×ˢ ball (0 : κ → ℝ) 3
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have hinj : InjOn π U := by
    intro x hx y hy hxy
    apply Prod.ext
    · exact congrArg (fun z : W => z.1) hxy
    funext j
    have hq := congrFun (congrArg (hamiltonLowerLatticePiEquiv κ)
      (congrArg Prod.snd hxy)) j
    change ((x.2 j : ℝ) : AddCircle (4 * (128 : ℝ))) =
      ((y.2 j : ℝ) : AddCircle (4 * (128 : ℝ))) at hq
    have hxx : |x.2 j| < 3 := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm x.2 j).trans_lt (mem_ball_zero_iff.mp hx.2)
    have hyy : |y.2 j| < 3 := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm y.2 j).trans_lt (mem_ball_zero_iff.mp hy.2)
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := 4 * (128 : ℝ)) (a := -256) ?_ ?_).mp hq
    · exact ⟨by linarith [(abs_lt.mp hxx).1], by linarith [(abs_lt.mp hxx).2]⟩
    · exact ⟨by linarith [(abs_lt.mp hyy).1], by linarith [(abs_lt.mp hyy).2]⟩
  have hq : IsCoveringMap
      (QuotientAddGroup.mk : (κ → ℝ) →
        ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup)) :=
    ((hamiltonLowerPeriodLattice κ).toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  have hπ : IsLocalHomeomorph π := hq.id_prod.isLocalHomeomorph
  let T : OpenPartialHomeomorph V W :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict hinj.toPartialEquiv
      hπ.continuous.continuousOn
      (hπ.isOpenMap.comp hU.isOpenMap_subtype_val) hU
  have hUs : U ⊆ h.source := by
    intro x hx
    have hc := I.core x.2 (mem_ball_zero_iff.mp hx.2).le
    have hxK : x.2 ∈ I.compactCarrier := by
      rw [← hc.2]
      exact I.image_subset ⟨QuotientAddGroup.mk x.2, hc.1, rfl⟩
    exact hsource ⟨hx.1, hxK⟩
  let e := T.symm.trans h
  have hpre (z : W) (hz : z ∈ e.source) :
      T.symm z ∈ U ∧ π (T.symm z) = z :=
    ⟨T.map_target hz.1, T.right_inv hz.1⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hy, heq⟩ := hpre z hz
    have hc := I.core (T.symm z).2 (mem_ball_zero_iff.mp hy.2).le
    rw [← heq]
    exact ⟨hy.1, hc.1⟩
  · intro z hz
    obtain ⟨hy, heq⟩ := hpre z hz
    have hc := I.core (T.symm z).2 (mem_ball_zero_iff.mp hy.2).le
    change h (T.symm z) = h (z.1, I.map z.2)
    apply congrArg h
    apply Prod.ext
    · exact congrArg (fun w : W => w.1) heq
    · have heq₂ : QuotientAddGroup.mk (T.symm z).2 = z.2 := congrArg Prod.snd heq
      rw [← heq₂, hc.2]
  · intro x hx
    have hxU : x ∈ U :=
      ⟨closedBall_subset_ball hb hx.1, closedBall_subset_ball (by norm_num) hx.2⟩
    have hTx : T.symm (π x) = x := T.left_inv hxU
    refine ⟨⟨T.map_source hxU, ?_⟩, ?_⟩
    · change T.symm (π x) ∈ h.source
      rw [hTx]
      exact hUs hxU
    · change h (T.symm (π x)) = h x
      rw [hTx]

end PoincareConjecture.M76
