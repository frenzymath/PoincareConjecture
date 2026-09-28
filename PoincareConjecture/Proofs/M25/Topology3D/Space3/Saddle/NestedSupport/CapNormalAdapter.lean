import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonExteriorHalfStrip
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_two_circle_positive_normal_collar
    (B : Fin 2 → BallNeighborhoodChart E2 E2)
    (c : Fin 2 → UnitCircle → E2)
    (hc : ∀ i, IsPlanarEmbedding (c i))
    (hDb : ∀ i, (B i).boundary = range (c i))
    (v : E2) (eta : ℝ) (heta : 0 < eta)
    (gamma : ℝ → E2)
    (Z : OpenPartialHomeomorph UnitCircle ℝ)
    (hZtarget : Z.target = Ioo (-eta) (1 + eta))
    (hJcZ : {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ} ⊆ Z.source)
    (hZ : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ Z Z.source)
    (hZi : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ Z.symm Z.target)
    (hcommon : ∀ i p, p ∈ Z.source → c i p = gamma (Z p))
    (N0 : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (hN0source : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ N0.source)
    (hN0 : ContDiffOn ℝ ∞ N0 N0.source)
    (hN0i : ContDiffOn ℝ ∞ N0.symm N0.target)
    (hN0zero : ∀ t ∈ Ioo (-eta) (1 + eta), N0 (t, 0) = gamma t)
    (path : ℝ → E2) (hpathC : ContinuousAt path 0)
    (hpath0 : path 0 = gamma (1 / 2))
    (d : ℝ) (hd : 0 < d)
    (hpathOutside : ∀ t ∈ Ioo (0 : ℝ) d, ∀ i,
      path t ∈ (B i).closedRegionᶜ) :
    ∃ (Uc : Set UnitCircle) (w : ℝ)
      (N : OpenPartialHomeomorph (UnitCircle × ℝ) E2),
      IsOpen Uc ∧
      {p : UnitCircle | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ} ⊆ Uc ∧
      Uc ⊆ {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ} ∧
      0 < w ∧
      Uc ×ˢ Icc (-w) w ⊆ N.source ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ N N.source ∧
      ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ N.symm N.target ∧
      (∀ p ∈ Uc, N (p, 0) = c 0 p) ∧
      (∀ i, N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ (B i).closedRegionᶜ) := by
  classical
  let Jc : Set UnitCircle :=
    {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  let Ac : Set UnitCircle :=
    {p : UnitCircle | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let B4 : Fin 4 → BallNeighborhoodChart E2 E2 :=
    fun a => B (ep.symm a).2
  let c4 : Fin 4 → UnitCircle → E2 := fun a => c (ep.symm a).2
  have hc4 (a : Fin 4) : IsPlanarEmbedding (c4 a) := hc _
  have hDb4 (a : Fin 4) : (B4 a).boundary = range (c4 a) := hDb _
  have hcommon4 (a : Fin 4) (p : UnitCircle) (hp : p ∈ Z.source) :
      c4 a p = gamma (Z p) := hcommon _ p hp
  have hInner : Continuous (fun p : UnitCircle => ⟪v, (p : E2)⟫_ℝ) :=
    continuous_const.inner continuous_subtype_val
  have hAcCompact : IsCompact Ac := by
    dsimp [Ac]
    exact (isClosed_le continuous_const hInner).isCompact
  have hJcOpen : IsOpen Jc := by
    dsimp [Jc]
    exact isOpen_lt continuous_const hInner
  have hAcJc : Ac ⊆ Jc := by
    intro p hp
    change (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ
    change (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ at hp
    linarith
  have hAcZ : Ac ⊆ Z.source := hAcJc.trans hJcZ
  let T : Set ℝ := Z '' Ac ∪ ({0, 1} : Set ℝ)
  have hTcompact : IsCompact T := by
    exact (hAcCompact.image_of_continuousOn (Z.continuousOn.mono hAcZ)).union
      (isCompact_singleton.insert 0)
  have hTtarget : T ⊆ Ioo (-eta) (1 + eta) := by
    intro t ht
    rcases ht with ht | ht
    · rcases ht with ⟨p, hp, rfl⟩
      rw [← hZtarget]
      exact Z.map_source (hAcZ hp)
    · rcases ht with (rfl | rfl) <;> constructor <;> linarith
  have hTne : T.Nonempty := ⟨0, by simp [T]⟩
  obtain ⟨tmin, htmin, hmin⟩ := hTcompact.exists_isMinOn hTne continuousOn_id
  obtain ⟨tmax, htmax, hmax⟩ := hTcompact.exists_isMaxOn hTne continuousOn_id
  have hminTarget : tmin ∈ Ioo (-eta) (1 + eta) := hTtarget htmin
  have hmaxTarget : tmax ∈ Ioo (-eta) (1 + eta) := hTtarget htmax
  let L : ℝ := (-eta + tmin) / 2
  let R : ℝ := (tmax + (1 + eta)) / 2
  have hL : -eta < L ∧ L < tmin := by
    dsimp [L]
    constructor <;> linarith [hminTarget.1]
  have hR : tmax < R ∧ R < 1 + eta := by
    dsimp [R]
    constructor <;> linarith [hmaxTarget.2]
  have hL0 : L < 0 := by
    have hm : tmin ≤ 0 := by
      simpa using hmin (by simp [T])
    linarith [hL.2]
  have h1R : 1 < R := by
    have hm : 1 ≤ tmax := by
      simpa using hmax (by simp [T])
    linarith [hR.1]
  have hLR : L < R := by linarith
  let Uc : Set UnitCircle := (Z.source ∩ Z ⁻¹' Ioo L R) ∩ Jc
  have hUc : IsOpen Uc := (Z.isOpen_inter_preimage isOpen_Ioo).inter hJcOpen
  have hAcUc : Ac ⊆ Uc := by
    intro p hp
    have hminp : tmin ≤ Z p := by
      simpa using hmin (show Z p ∈ T from Or.inl ⟨p, hp, rfl⟩)
    have hmaxp : Z p ≤ tmax := by
      simpa using hmax (show Z p ∈ T from Or.inl ⟨p, hp, rfl⟩)
    exact ⟨⟨hAcZ hp, ⟨hL.2.trans_le hminp, hmaxp.trans_lt hR.1⟩⟩,
      hAcJc hp⟩
  have hUcJc : Uc ⊆ Jc := inter_subset_right
  have hNsource : Ioo (-eta) (1 + eta) ×ˢ ({0} : Set ℝ) ⊆ N0.source := hN0source
  have hNzero (t : ℝ) (ht : t ∈ Ioo (-eta) (1 + eta)) :
      N0 (t, 0) = gamma t := hN0zero t ht
  have hhalf : ∃ (w sigma : ℝ), 0 < w ∧ (sigma = 1 ∨ sigma = -1) ∧
      Icc L R ×ˢ Icc (-w) w ⊆ N0.source ∧
      ∀ a : Fin 4,
        N0 '' (Ioo L R ×ˢ {z : ℝ | 0 < sigma * z ∧ |z| < w}) ⊆
          (B4 a).closedRegionᶜ := by
    exact exists_saddle_common_exterior_half_strip B4 c4 hc4 hDb4 Z gamma
      (-eta) (1 + eta) L R hL.1 hLR hR.2 hZtarget hcommon4 N0 hNsource hNzero
      (1 / 2) ⟨by linarith [hL0], by linarith [h1R]⟩ path hpathC hpath0 d hd
      (fun t ht a => hpathOutside t ht (ep.symm a).2)
  obtain ⟨w, sigma, hw, hsign, hrect, hpositive⟩ := hhalf
  have hsignSq : sigma * sigma = 1 := by
    rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  have hsignAbs : |sigma| = 1 := by
    rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  let Ref : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := {
    toFun := fun p => (p.1, sigma * p.2)
    invFun := fun p => (p.1, sigma * p.2)
    source := univ
    target := univ
    map_source' := fun _ _ => mem_univ _
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun p _ => by
      apply Prod.ext
      · rfl
      · change sigma * (sigma * p.2) = p.2
        rw [← mul_assoc, hsignSq, one_mul]
    right_inv' := fun p _ => by
      apply Prod.ext
      · rfl
      · change sigma * (sigma * p.2) = p.2
        rw [← mul_assoc, hsignSq, one_mul]
    open_source := isOpen_univ
    open_target := isOpen_univ
    continuousOn_toFun :=
      (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
    continuousOn_invFun :=
      (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn }
  have hRef : ContDiff ℝ ∞ (Ref : (ℝ × ℝ) → (ℝ × ℝ)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  have hRefInv : ContDiff ℝ ∞ (Ref.symm : (ℝ × ℝ) → (ℝ × ℝ)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  let P := Z.prod (OpenPartialHomeomorph.refl ℝ)
  have hPs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      P P.source := by
    have hp : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ P P.source :=
      hZ.prodMap contMDiff_id.contMDiffOn
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
    exact hp
  have hPi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      P.symm P.target := by
    have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ P.symm P.target :=
      hZi.prodMap contMDiff_id.contMDiffOn
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
    exact hp
  let N : OpenPartialHomeomorph (UnitCircle × ℝ) E2 :=
    (P.trans Ref).trans N0
  have hNform (p : UnitCircle) (s : ℝ) :
      N (p, s) = N0 (Z p, sigma * s) := rfl
  have hNs : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ N N.source := by
    have hp : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
        (P.trans Ref) (P.trans Ref).source := by
      exact (hRef.contDiffOn.contMDiffOn).comp
        (hPs.mono inter_subset_left) (fun _ hp => hp.2)
    exact hN0.contMDiffOn.comp (hp.mono inter_subset_left) (fun _ hp => hp.2)
  have hNi : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      N.symm N.target := by
    have hp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        (P.trans Ref).symm (P.trans Ref).target := by
      exact hPi.comp (hRefInv.contDiffOn.contMDiffOn.mono inter_subset_left)
        (fun _ hp => hp.2)
    exact hp.comp (hN0i.contMDiffOn.mono inter_subset_left) (fun _ hp => hp.2)
  have hNbuffer : Uc ×ˢ Icc (-w) w ⊆ N.source := by
    rintro ⟨p, s⟩ ⟨hp, hs⟩
    refine ⟨⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩, ?_⟩
    change (Z p, sigma * s) ∈ N0.source
    apply hrect
    have habs : |sigma * s| ≤ w := by
      rw [abs_mul, hsignAbs, one_mul]
      exact abs_le.mpr hs
    exact ⟨⟨hp.1.2.1.le, hp.1.2.2.le⟩, abs_le.mp habs⟩
  have hNzero' (p : UnitCircle) (hp : p ∈ Uc) : N (p, 0) = c 0 p := by
    rw [hNform, mul_zero, hNzero (Z p) (by rw [← hZtarget]; exact Z.map_source hp.1.1)]
    exact (hcommon 0 p hp.1.1).symm
  have hNpositive (i : Fin 2) :
      N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ (B i).closedRegionᶜ := by
    rintro x ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
    rw [hNform]
    have hmul : 0 < sigma * (sigma * s) := by
      rw [← mul_assoc, hsignSq, one_mul]
      exact hs.1
    have habs : |sigma * s| < w := by
      rw [abs_mul, hsignAbs, one_mul, abs_of_pos hs.1]
      exact hs.2
    have hi := hpositive (ep (0, i))
      ⟨(Z p, sigma * s), ⟨hp.1.2, hmul, habs⟩, rfl⟩
    simpa only [B4, Equiv.symm_apply_apply] using hi
  exact ⟨Uc, w, N, hUc, hAcUc, hUcJc, hw, hNbuffer, hNs, hNi,
    hNzero', fun i => hNpositive i⟩

end PoincareConjecture.M25.Topology3D
