import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseGraphShear











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackMorseGraphNormalization
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho r0 : ℝ) (hkappa : |kappa| = 1)
    (hr0 : 0 < r0) (hr0rho : r0 < rho)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (S : Set E3)
    (hgraph : ∀ p ∈ A.source, A p ∈ S ↔ p.2 = c + kappa * ‖p.1‖ ^ 2)
    (g : E2 → ℝ) (U : Set E2) (hU : IsOpen U)
    (hdiscU : closedBall (0 : E2) rho ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hbound : ∀ x ∈ closedBall (0 : E2) rho,
      ‖x‖ ^ 2 ≤ g x ∧ g x ≤ rho ^ 2)
    (hseam : ∀ x ∈ closedBall (0 : E2) rho,
      r0 ≤ ‖x‖ → g x = ‖x‖ ^ 2) :
    let original : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
    let replacement : E2 → E3 := fun x => A (x, c + kappa * g x)
    let disc : Set E3 := original '' closedBall (0 : E2) rho
    let discOpen : Set E3 := original '' ball (0 : E2) rho
    let seam : Set E3 := original '' sphere (0 : E2) rho
    let rest : Set E3 := S \ discOpen
    let cap : Set E3 := replacement '' closedBall (0 : E2) rho
    ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ C N : Set E3,
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
        (∀ y, Phi 0 y = y) ∧
        (∀ x ∈ closedBall (0 : E2) rho, ∀ t ∈ Icc (0 : ℝ) 1,
          Phi t (original x) =
            A (x, c + kappa * ((1 - t) * ‖x‖ ^ 2 + t * g x))) ∧
        IsCompact C ∧
        C ⊆ A '' (closedBall (0 : E2) r0 ×ˢ
          Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)) ∧
        (∀ t, tsupport (fun y => Phi t y - y) ⊆ C) ∧
        (∀ t, tsupport (fun y => (Phi t).symm y - y) ⊆ C) ∧
        IsOpen N ∧ rest ⊆ N ∧ Disjoint N C ∧
        (∀ t y, y ∈ N → Phi t y = y ∧ (Phi t).symm y = y) ∧
        disc ⊆ S ∧ disc \ discOpen = seam ∧
        Phi 1 '' disc = cap ∧ (Phi 1).symm '' cap = disc ∧
        rest ∩ cap = seam ∧ Phi 1 '' S = rest ∪ cap := by
  classical
  let original : E2 → E3 := fun x => A (x, c + kappa * ‖x‖ ^ 2)
  let replacement : E2 → E3 := fun x => A (x, c + kappa * g x)
  let disc : Set E3 := original '' closedBall (0 : E2) rho
  let discOpen : Set E3 := original '' ball (0 : E2) rho
  let seam : Set E3 := original '' sphere (0 : E2) rho
  let rest : Set E3 := S \ discOpen
  let cap : Set E3 := replacement '' closedBall (0 : E2) rho
  have hrho : 0 < rho := hr0.trans hr0rho
  have horiginal (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      (x, c + kappa * ‖x‖ ^ 2) ∈ A.source := by
    have hn := mem_closedBall_zero_iff.mp hx
    have hsq : ‖x‖ ^ 2 ≤ rho ^ 2 := by nlinarith only [hn, norm_nonneg x, hrho]
    have habs : |kappa * ‖x‖ ^ 2| ≤ rho ^ 2 := by
      rw [abs_mul, hkappa, one_mul, abs_of_nonneg (sq_nonneg _)]
      exact hsq
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    apply hsource
    refine ⟨mem_closedBall_zero_iff.mpr (by linarith only [hn, hrho]), ?_, ?_⟩
    · linarith only [hlo, sq_nonneg rho]
    · linarith only [hhi, sq_nonneg rho]
  have hsmall (p : E2 × ℝ)
      (hp : p ∈ closedBall (0 : E2) r0 ×ˢ
        Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)) : p ∈ A.source := by
    have hn := mem_closedBall_zero_iff.mp hp.1
    exact hsource ⟨mem_closedBall_zero_iff.mpr (by linarith only [hn, hr0rho, hrho]),
      hp.2.1.le, hp.2.2.le⟩
  obtain ⟨d, hd, _hdc, hds, hdf, hdb, _hdzero⟩ :=
    exists_stackMorseGraphDisplacement rho r0 hr0 hr0rho g U hU hdiscU hg hbound hseam
  obtain ⟨Phi, C, hPhi, hPhii, hPhi0, htrack, hC, hCsub, hs, hsi, hfix⟩ :=
    exists_stackMorseGraphShear A hA hAi c kappa rho r0 hkappa hr0 hr0rho hsource d hd hds hdb
  have hconvex (x : E2) (hx : x ∈ closedBall (0 : E2) rho)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Phi t (original x) = A (x, c + kappa * ((1 - t) * ‖x‖ ^ 2 + t * g x)) := by
    change Phi t (A (x, c + kappa * ‖x‖ ^ 2)) = _
    rw [htrack x hx t ht, hdf x hx]
    have he : ‖x‖ ^ 2 + t * (g x - ‖x‖ ^ 2) =
        (1 - t) * ‖x‖ ^ 2 + t * g x := by ring
    rw [he]
  have hend (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      Phi 1 (original x) = replacement x := by
    simpa only [replacement, sub_self, zero_mul, one_mul, zero_add] using
      hconvex x hx 1 (by norm_num)
  have hdiscS : disc ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hgraph _ (horiginal x hx)).mpr rfl
  have hopenDisc : discOpen ⊆ disc := image_mono ball_subset_closedBall
  have hinj : Set.InjOn original (closedBall (0 : E2) rho) := by
    intro x hx y hy he
    exact congrArg Prod.fst (A.injOn (horiginal x hx) (horiginal y hy) he)
  have hboundary : disc \ discOpen = seam := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      have hnot : ¬‖x‖ < rho := fun h => hn ⟨x, mem_ball_zero_iff.mpr h, rfl⟩
      exact ⟨x, mem_sphere_zero_iff_norm.mpr
        (le_antisymm (mem_closedBall_zero_iff.mp hx) (le_of_not_gt hnot)), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, sphere_subset_closedBall hx, rfl⟩, ?_⟩
      rintro ⟨v, hv, he⟩
      have hvx := hinj (ball_subset_closedBall hv) (sphere_subset_closedBall hx) he
      have hn := mem_ball_zero_iff.mp hv
      rw [hvx, mem_sphere_zero_iff_norm.mp hx] at hn
      exact lt_irrefl _ hn
  have hCS : C ∩ S ⊆ discOpen := by
    rintro y ⟨hyC, hyS⟩
    obtain ⟨p, hp, rfl⟩ := hCsub hyC
    have hpz := (hgraph p (hsmall p hp)).mp hyS
    refine ⟨p.1, mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.1).trans_lt hr0rho), ?_⟩
    change A (p.1, c + kappa * ‖p.1‖ ^ 2) = A p
    exact congrArg A (Prod.ext rfl hpz.symm)
  have hrestN : rest ⊆ Cᶜ := by
    intro y hy hyC
    exact hy.2 (hCS ⟨hyC, hy.1⟩)
  have himage : Phi 1 '' disc = cap := by
    change Phi 1 '' (original '' closedBall (0 : E2) rho) =
      replacement '' closedBall (0 : E2) rho
    rw [image_image]
    exact image_congr (fun x hx => hend x hx)
  have hinverse : (Phi 1).symm '' cap = disc := by
    rw [← himage, image_image]
    simp only [Diffeomorph.symm_apply_apply]
    exact image_id disc
  have hcross : rest ∩ cap = seam := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨hyr, hyc⟩
      have hyimage : y ∈ Phi 1 '' disc := himage.symm ▸ hyc
      obtain ⟨x, hx, hxy⟩ := hyimage
      have he : x = y := by
        have hh := congrArg (Phi 1).symm hxy
        simpa only [Diffeomorph.symm_apply_apply, (hfix 1 y (hrestN hyr)).2] using hh
      exact hboundary ▸ show y ∈ disc \ discOpen from ⟨he ▸ hx, hyr.2⟩
    · intro hy
      have hyd : y ∈ disc \ discOpen := hboundary.symm ▸ hy
      have hyr : y ∈ rest := ⟨hdiscS hyd.1, hyd.2⟩
      refine ⟨hyr, himage ▸ ?_⟩
      exact ⟨y, hyd.1, (hfix 1 y (hrestN hyr)).1⟩
  have hcover : S = rest ∪ disc := by
    apply Set.ext
    intro y
    constructor
    · intro hy
      by_cases ho : y ∈ discOpen
      · exact Or.inr (hopenDisc ho)
      · exact Or.inl ⟨hy, ho⟩
    · rintro (hy | hy)
      · exact hy.1
      · exact hdiscS hy
  have hrestImage : Phi 1 '' rest = rest := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (hfix 1 y (hrestN hy)).1.symm ▸ hy
    · intro y hy
      exact ⟨y, hy, (hfix 1 y (hrestN hy)).1⟩
  refine ⟨Phi, C, Cᶜ, hPhi, hPhii, hPhi0, hconvex, hC, hCsub, hs, hsi,
    hC.isClosed.isOpen_compl, hrestN, disjoint_compl_left, hfix, hdiscS,
    hboundary, himage, hinverse, hcross, ?_⟩
  calc
    Phi 1 '' S = Phi 1 '' (rest ∪ disc) := congrArg (fun V => Phi 1 '' V) hcover
    _ = rest ∪ cap := by rw [image_union, hrestImage, himage]

end PoincareConjecture.M25.Topology3D
