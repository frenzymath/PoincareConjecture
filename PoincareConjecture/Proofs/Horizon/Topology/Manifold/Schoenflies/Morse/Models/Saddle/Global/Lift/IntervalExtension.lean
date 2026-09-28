import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff











noncomputable section
set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

private theorem contDiff_localized_height_family
    {U : Set Real} (hU : IsOpen U)
    {χ : Real → Real} (hχ : ContDiff Real ∞ χ) (hsχ : tsupport χ ⊆ U)
    (f : Real × Real × E2 → E2)
    (hf : ContDiffOn Real ∞ f (univ ×ˢ (U ×ˢ univ)))
    (f0 : ∀ z ∈ U, ∀ x, f (0, z, x) = x)
    (g : Real × E2 → E2)
    (hg : ∀ z ∈ U, ∀ x, g (z, x) = f (χ z, z, x))
    (hg0 : ∀ z ∉ U, ∀ x, g (z, x) = x) :
    ContDiff Real ∞ g := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ U
  · have hf' : ContDiffAt Real ∞ f (χ p.1, p.1, p.2) :=
      (hf _ ⟨mem_univ _, hp, mem_univ _⟩).contDiffAt
        ((isOpen_univ.prod (hU.prod isOpen_univ)).mem_nhds
          ⟨mem_univ _, hp, mem_univ _⟩)
    apply (hf'.comp (f := fun q : Real × E2 => (χ q.1, q)) p
      ((hχ.comp contDiff_fst).prodMk contDiff_id).contDiffAt).congr_of_eventuallyEq
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hp] with q hq
    exact hg q.1 hq q.2
  · have hn : p.1 ∉ tsupport χ := fun h => hp (hsχ h)
    have he : ∀ᶠ q : Real × E2 in 𝓝 p, χ q.1 = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto continuous_fst.continuousAt
    apply (contDiff_snd.contDiffAt : ContDiffAt Real ∞ Prod.snd p).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    by_cases hqU : q.1 ∈ U
    · rw [hg q.1 hqU, hq, f0 q.1 hqU]
    · exact hg0 q.1 hqU q.2




theorem exists_interval_supported_planar_family
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a b : Real} {U : Set Real} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hΦ : ContDiffOn Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hΦinv : ContDiffOn Real ∞
      (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hzero : ∀ z ∈ U, ∀ x, Φ 0 z x = x)
    {K : Set E2} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : Real) 1, ∀ z ∈ U, ∀ x ∉ K, Φ t z x = x)
    {ε : Real} (hε : 0 < ε) :
    ∃ Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun q : Real × E2 => Ψ q.1 q.2) ∧
      ContDiff Real ∞ (fun q : Real × E2 => (Ψ q.1).symm q.2) ∧
      (∀ z ∈ Icc a b, Ψ z = Φ 1 z) ∧
      (∀ z x, x ∉ K → Ψ z x = x) ∧
      (∀ z, z ≤ a - ε ∨ b + ε ≤ z → ∀ x, Ψ z x = x) ∧
      HasCompactSupport (fun q : Real × E2 => Ψ q.1 q.2 - q.2) ∧
      HasCompactSupport (fun q : Real × E2 => (Ψ q.1).symm q.2 - q.2) := by
  classical
  have hIU : Icc a b ⊆ U ∩ Ioo (a - ε) (b + ε) := by
    intro z hz
    exact ⟨hI hz, by constructor <;> linarith [hz.1, hz.2]⟩
  obtain ⟨χ, hχ, _, hsχ, hχrange, hχone, _⟩ :=
    Poincare.Manifold.exists_compact_smooth_cutoff 𝓘(Real, Real)
      isCompact_Icc (hU.inter isOpen_Ioo) hIU
  have hχsmooth : ContDiff Real ∞ χ := hχ.contDiff
  have hχU : tsupport χ ⊆ U := hsχ.trans inter_subset_left
  let Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun z => if z ∈ U then Φ (χ z) z else Diffeomorph.refl (𝓡 2) E2 ∞
  have hΨ (z : Real) (hz : z ∈ U) : Ψ z = Φ (χ z) z := if_pos hz
  have hΨzero (z : Real) (hz : z ∉ U) :
      Ψ z = Diffeomorph.refl (𝓡 2) E2 ∞ := if_neg hz
  have hΨsmooth : ContDiff Real ∞ (fun q : Real × E2 => Ψ q.1 q.2) := by
    apply contDiff_localized_height_family hU hχsmooth hχU
      (fun q => Φ q.1 q.2.1 q.2.2) hΦ hzero
    · intro z hz x
      rw [hΨ z hz]
    · intro z hz x
      rw [hΨzero z hz]
      rfl
  have hΨinv : ContDiff Real ∞ (fun q : Real × E2 => (Ψ q.1).symm q.2) := by
    apply contDiff_localized_height_family hU hχsmooth hχU
      (fun q => (Φ q.1 q.2.1).symm q.2.2) hΦinv
    · intro z hz x
      apply (Φ 0 z).injective
      change Φ 0 z ((Φ 0 z).symm x) = Φ 0 z x
      rw [Diffeomorph.apply_symm_apply, hzero z hz]
    · intro z hz x
      rw [hΨ z hz]
    · intro z hz x
      rw [hΨzero z hz]
      rfl
  have hfix (z : Real) (x : E2) (hx : x ∉ K) : Ψ z x = x := by
    by_cases hz : z ∈ U
    · rw [hΨ z hz]
      exact hsupp (χ z) (hχrange z) z hz x hx
    · rw [hΨzero z hz]
      rfl
  have htail (z : Real) (hz : z ≤ a - ε ∨ b + ε ≤ z) (x : E2) : Ψ z x = x := by
    by_cases hzU : z ∈ U
    · have hzχ : z ∉ tsupport χ := by
        intro h
        have hi := (hsχ h).2
        rcases hz with hz | hz <;> linarith [hi.1, hi.2]
      rw [hΨ z hzU, image_eq_zero_of_notMem_tsupport hzχ, hzero z hzU]
    · rw [hΨzero z hzU]
      rfl
  have hcompact : IsCompact (Icc (a - ε) (b + ε) ×ˢ K) := isCompact_Icc.prod hK
  have houtside (q : Real × E2) (hq : q ∉ Icc (a - ε) (b + ε) ×ˢ K) :
      Ψ q.1 q.2 = q.2 := by
    by_cases hx : q.2 ∈ K
    · apply htail
      have ht : q.1 ∉ Icc (a - ε) (b + ε) := fun ht => hq ⟨ht, hx⟩
      rcases lt_or_ge q.1 (a - ε) with h | h
      · exact Or.inl h.le
      · exact Or.inr (not_le.mp (fun hb => ht ⟨h, hb⟩)).le
    · exact hfix q.1 q.2 hx
  refine ⟨Ψ, hΨsmooth, hΨinv, ?_, hfix, htail, ?_, ?_⟩
  · intro z hz
    rw [hΨ z (hI hz), hχone.self_of_nhdsSet z hz]
  · exact HasCompactSupport.intro hcompact (fun q hq => sub_eq_zero.mpr (houtside q hq))
  · apply HasCompactSupport.intro hcompact
    intro q hq
    apply sub_eq_zero.mpr
    apply (Ψ q.1).injective
    change Ψ q.1 ((Ψ q.1).symm q.2) = Ψ q.1 q.2
    rw [Diffeomorph.apply_symm_apply, houtside q hq]




theorem exists_interval_supported_height_lift
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a b : Real} {U : Set Real} (hU : IsOpen U) (hI : Icc a b ⊆ U)
    (hΦ : ContDiffOn Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hΦinv : ContDiffOn Real ∞
      (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2)
      (univ ×ˢ (U ×ˢ univ)))
    (hzero : ∀ z ∈ U, ∀ x, Φ 0 z x = x)
    {K : Set E2} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : Real) 1, ∀ z ∈ U, ∀ x ∉ K, Φ t z x = x)
    {ε : Real} (hε : 0 < ε) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, (H y) 2 = y 2) ∧
      (∀ y, y 2 ∈ Icc a b → H y = toE3 (Φ 1 (y 2) (toE2 y)) (y 2)) ∧
      (∀ y, y 2 ∈ Icc a b →
        H.symm y = toE3 ((Φ 1 (y 2)).symm (toE2 y)) (y 2)) ∧
      (∀ c ∈ Icc a b, ∀ S : Set E2, H '' slice S c = slice (Φ 1 c '' S) c) ∧
      (∀ L : Real → Set E2, H '' (⋃ c ∈ Icc a b, slice (L c) c) =
        ⋃ c ∈ Icc a b, slice (Φ 1 c '' L c) c) ∧
      (∀ y, toE2 y ∉ K → H y = y) ∧
      (∀ y, y 2 ≤ a - ε ∨ b + ε ≤ y 2 → H y = y) ∧
      HasCompactSupport (fun y => H y - y) ∧
      HasCompactSupport (fun y => H.symm y - y) := by
  obtain ⟨Ψ, hΨ, hΨinv, heq, hfix, htail, _, _⟩ :=
    exists_interval_supported_planar_family Φ hU hI hΦ hΦinv hzero hK hsupp hε
  obtain ⟨H, hH, hHi, hheight, hslice⟩ := exists_height_lift Ψ hΨ hΨinv
  have hcoord (y : E3) : toE3 (toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  have hspatial (y : E3) (hy : toE2 y ∉ K) : H y = y := by
    rw [hH, hfix _ _ hy, hcoord]
  have hexterior (y : E3) (hy : y 2 ≤ a - ε ∨ b + ε ≤ y 2) : H y = y := by
    rw [hH, htail _ hy, hcoord]
  have hC : IsCompact ((fun q : E2 × Real => toE3 q.1 q.2) ''
      (K ×ˢ Icc (a - ε) (b + ε))) := by
    apply (hK.prod isCompact_Icc).image
    unfold toE3
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have houtside (y : E3) (hy : y ∉ (fun q : E2 × Real => toE3 q.1 q.2) ''
      (K ×ˢ Icc (a - ε) (b + ε))) : H y = y := by
    by_cases hk : toE2 y ∈ K
    · apply hexterior
      have ht : y 2 ∉ Icc (a - ε) (b + ε) := fun ht =>
        hy ⟨(toE2 y, y 2), ⟨hk, ht⟩, hcoord y⟩
      rcases lt_or_ge (y 2) (a - ε) with h | h
      · exact Or.inl h.le
      · exact Or.inr (not_le.mp (fun hb => ht ⟨h, hb⟩)).le
    · exact hspatial y hk
  refine ⟨H, hheight, ?_, ?_, ?_, ?_, hspatial, hexterior, ?_, ?_⟩
  · intro y hy
    rw [hH, heq _ hy]
  · intro y hy
    rw [hHi, heq _ hy]
  · intro c hc S
    rw [hslice, heq c hc]
  · intro L
    rw [image_iUnion]
    apply iUnion_congr
    intro c
    rw [image_iUnion]
    apply iUnion_congr
    intro hc
    rw [hslice, heq c hc]
  · exact HasCompactSupport.intro hC (fun y hy => sub_eq_zero.mpr (houtside y hy))
  · apply HasCompactSupport.intro hC
    intro y hy
    apply sub_eq_zero.mpr
    apply H.injective
    change H (H.symm y) = H y
    rw [Diffeomorph.apply_symm_apply, houtside y hy]

end Poincare.Manifold.Schoenflies.Saddle
