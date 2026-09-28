import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneActualRetraction










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)
local notation "Q" => sphere (0 : V2) 1


def squareUnitBlock : Set W := Icc (-1) 1 ×ˢ closedBall 0 1


def squareCoreShell : Set W :=
  Icc (-1) 1 ×ˢ ((norm : V2 → ℝ) ⁻¹' Icc 1 2)

private theorem closure_block_without_unit :
    closure (squareBlock \ squareUnitBlock) = squareCoreShell := by
  have hclosed : IsClosed squareCoreShell :=
    isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm)
  refine Subset.antisymm (closure_minimal ?_ hclosed) ?_
  · intro x hx
    refine ⟨hx.1.1, ?_, mem_closedBall_zero_iff.mp hx.1.2⟩
    by_contra hn
    exact hx.2 ⟨hx.1.1, mem_closedBall_zero_iff.mpr (lt_of_not_ge hn).le⟩
  · intro x hx
    by_cases hr : 1 < ‖x.2‖
    · exact subset_closure ⟨⟨hx.1, mem_closedBall_zero_iff.mpr hx.2.2⟩,
        fun hc => (not_lt_of_ge (mem_closedBall_zero_iff.mp hc.2)) hr⟩
    · have heq : ‖x.2‖ = 1 := le_antisymm (not_lt.mp hr) hx.2.1
      let f : ℝ → W := fun t => (x.1, t • x.2)
      have hf : Continuous f := continuous_const.prodMk (continuous_id.smul continuous_const)
      have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖(f t).2‖ = t := by
        change ‖t • x.2‖ = t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, heq, mul_one]
      have hmaps : MapsTo f (Ioc (1 : ℝ) 2) (squareBlock \ squareUnitBlock) := by
        intro t ht
        have ht0 : 0 ≤ t := by linarith [ht.1]
        refine ⟨⟨hx.1, mem_closedBall_zero_iff.mpr ?_⟩, ?_⟩
        · rw [hnorm t ht0]
          exact ht.2
        · intro hc
          have h := mem_closedBall_zero_iff.mp hc.2
          rw [hnorm t ht0] at h
          exact (not_lt_of_ge h) ht.1
      have hbase : (1 : ℝ) ∈ closure (Ioc (1 : ℝ) 2) := by
        rw [closure_Ioc (by norm_num : (1 : ℝ) ≠ 2)]
        constructor <;> norm_num
      have hlim := hf.continuousWithinAt.mem_closure hbase hmaps
      simpa only [f, one_smul, Prod.mk.eta] using hlim




theorem coreExterior_image_unit (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock) :
    coreExterior (A '' squareUnitBlock) = A '' squareCoreShell := by
  have hdiff : A '' (squareBlock \ squareUnitBlock) =
      squareBlock \ (A '' squareUnitBlock) := by
    rw [image_sdiff A.injective, hAL]
  rw [coreExterior, ← hdiff, ← A.image_closure, closure_block_without_unit]




theorem exists_actual_core_angular_map
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (hAf : EqOn A id (frontier squareBlock)) :
    ∃ rho : C(coreExterior (A '' squareUnitBlock), Q),
      (∀ y : coreExterior (A '' squareUnitBlock),
        (A.symm (y : W)).2 = ‖(A.symm (y : W)).2‖ • (rho y : V2)) ∧
      ∀ (s : ℝ), s = -1 ∨ s = 1 → ∀ (u : Q)
        (y : coreExterior (A '' squareUnitBlock)),
        (y : W) = (s, (3 / 2 : ℝ) • (u : V2)) → rho y = u := by
  let E0 := coreExterior (A '' squareUnitBlock)
  have hmem (y : E0) : A.symm (y : W) ∈ squareCoreShell := by
    have hy : (y : W) ∈ A '' squareCoreShell := coreExterior_image_unit A hAL ▸ y.property
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, A.symm_apply_apply]
    exact hx
  let free : C(E0, V2) :=
    ⟨fun y => (A.symm (y : W)).2,
      continuous_snd.comp (A.symm.continuous.comp continuous_subtype_val)⟩
  have hn (y : E0) : 0 < ‖free y‖ := lt_of_lt_of_le (by norm_num) (hmem y).2.1
  let rho : C(E0, Q) :=
    ⟨fun y => ⟨‖free y‖⁻¹ • free y, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hn y),
        inv_mul_cancel₀ (hn y).ne'])⟩,
      ((free.continuous.norm.inv₀ (fun y => (hn y).ne')).smul free.continuous).subtype_mk _⟩
  refine ⟨rho, ?_, ?_⟩
  · intro y
    change free y = ‖free y‖ • (‖free y‖⁻¹ • free y)
    rw [smul_smul, mul_inv_cancel₀ (hn y).ne', one_smul]
  · intro s hs u y hy
    have hu : ‖(u : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    have hv : ‖(3 / 2 : ℝ) • (u : V2)‖ = (3 / 2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
        hu, mul_one]
    have hsI : s ∈ Icc (-1 : ℝ) 1 := by
      rcases hs with hs | hs <;> rw [hs] <;> norm_num
    have hpoint : (s, (3 / 2 : ℝ) • (u : V2)) ∈ frontier squareBlock := by
      refine ⟨subset_closure ⟨hsI, mem_closedBall_zero_iff.mpr (by rw [hv]; norm_num)⟩, ?_⟩
      intro hi
      rw [squareBlock, interior_prod_eq, interior_Icc] at hi
      rcases hs with hs | hs
      · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hi.1.1)
      · exact (lt_irrefl (1 : ℝ)) (hs ▸ hi.1.2)
    have hAi : A.symm (y : W) = (s, (3 / 2 : ℝ) • (u : V2)) := by
      apply A.injective
      rw [A.apply_symm_apply]
      exact hy.trans (hAf hpoint).symm
    have hfree : free y = (3 / 2 : ℝ) • (u : V2) := congrArg Prod.snd hAi
    apply Subtype.ext
    change ‖free y‖⁻¹ • free y = (u : V2)
    rw [hfree, hv, smul_smul, inv_mul_cancel₀ (by norm_num : (3 / 2 : ℝ) ≠ 0), one_smul]





theorem exists_same_A_complement_retraction
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (hAf : EqOn A id (frontier squareBlock)) {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (hKB : A '' squareUnitBlock ⊆ B) (hKT : Disjoint (A '' squareUnitBlock) T) :
    complementaryRegion B ⊆ coreExterior (A '' squareUnitBlock) ∧
      ∃ r : C(coreExterior (A '' squareUnitBlock), complementaryRegion B),
        ∀ x : coreExterior (A '' squareUnitBlock),
          (x : W) ∈ complementaryRegion B → (r x : W) = x := by
  obtain ⟨rho, _, hrho⟩ := exists_actual_core_angular_map A hAL hAf
  have hK : IsCompact (A '' squareUnitBlock) :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : V2) 1)).image A.continuous
  exact exists_actual_complement_retraction hB hBL hT hcontact hrims tau htau hfix
    hK hKB hKT rho (fun u y hy => hrho (-1) (Or.inl rfl) u y hy)

end PoincareConjecture.M76.HamiltonIndexOne
