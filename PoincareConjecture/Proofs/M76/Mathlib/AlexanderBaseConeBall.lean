import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeExtension
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LinearMap.mem_base_union_convexJoin_iff (L : E →ₗ[ℝ] ℝ)
    {s b : Set E} (hb : b ⊆ s) (hbne : b.Nonempty)
    (hL : ∀ x ∈ s, L x = 1) {y : E} (hy : y ∈ s)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    r • y ∈ s ∪ convexJoin ℝ {0} b ↔ r = 0 ∨ r = 1 ∨ y ∈ b := by
  constructor
  · rintro (hs | hs)
    · right
      left
      have h := hL (r • y) hs
      simpa only [map_smul, hL y hy, smul_eq_mul, mul_one] using h
    · obtain ⟨z, hz, t, _, hrt⟩ := (mem_convexJoin_zero_iff b _).mp hs
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · have hrt' : r = t := by
          have h := congrArg L hrt
          simpa only [map_smul, hL y hy, hL z (hb hz), smul_eq_mul, mul_one] using h
        subst t
        exact Or.inr (Or.inr ((smul_right_injective E hr0 hrt).symm ▸ hz))
  · rintro (hr0 | hr1 | hyb)
    · right
      obtain ⟨z, hz⟩ := hbne
      exact (mem_convexJoin_zero_iff b _).mpr
        ⟨z, hz, 0, ⟨le_rfl, zero_le_one⟩, by simp [hr0]⟩
    · left
      simpa only [hr1, one_smul] using hy
    · right
      exact (mem_convexJoin_zero_iff b _).mpr ⟨y, hyb, r, hr, rfl⟩

namespace Set

variable [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.convexJoin_zero {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (L : E →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ d, L x = 1) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {0} d)
      (d ∪ convexJoin ℝ {0} q) := by
  obtain ⟨e, he, heb⟩ := hd.exists_homeomorph AlexanderBaseConeModel.isFinitePLBallPair_top
  have hdne : d.Nonempty := hd.sdiff_nonempty.mono sdiff_subset
  have hqne : q.Nonempty := by
    obtain ⟨z, hz⟩ := AlexanderBaseConeModel.rim_nonempty
    let w : AlexanderBaseConeModel.top :=
      ⟨z, AlexanderBaseConeModel.isFinitePLBallPair_top.1 hz⟩
    refine ⟨e.symm w, (heb (e.symm w)).mpr ?_⟩
    simpa only [e.apply_symm_apply] using hz
  let M := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hM (z : ((ℝ × ℝ) × ℝ)) (hz : z ∈ AlexanderBaseConeModel.top) : M z = 1 :=
    AlexanderBaseConeModel.height_top z hz
  obtain ⟨H, hH, hHr⟩ := he.exists_radial_cone_extension hdne L M hL hM
  have hbd : d ∪ convexJoin ℝ {0} q ⊆ convexJoin ℝ {0} d := by
    apply union_subset
    · exact subset_convexJoin_right (singleton_nonempty (0 : E))
    · exact convexJoin_mono_right hd.1
  apply AlexanderBaseConeModel.isFinitePLBallPair_cone.of_homeomorph hbd H hH
  intro x
  obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff d _).mp x.property
  have hval : (H x : (ℝ × ℝ) × ℝ) = r • (e ⟨y, hy⟩ : (ℝ × ℝ) × ℝ) := by
    have hx : x = ⟨r • y, (mem_convexJoin_zero_iff d _).mpr ⟨y, hy, r, hr, rfl⟩⟩ :=
      Subtype.ext hxy
    rw [hx]
    exact hHr ⟨y, hy⟩ r hr
  rw [hval, hxy, L.mem_base_union_convexJoin_iff hd.1 hqne hL hy hr,
    M.mem_base_union_convexJoin_iff AlexanderBaseConeModel.isFinitePLBallPair_top.1
      AlexanderBaseConeModel.rim_nonempty hM (e ⟨y, hy⟩).property hr,
    heb ⟨y, hy⟩]

end Set
