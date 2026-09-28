import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackMorseGraphDisplacement
    (rho r0 : ℝ) (hr0 : 0 < r0) (hr0rho : r0 < rho)
    (g : E2 → ℝ) (U : Set E2) (hU : IsOpen U)
    (hdiscU : closedBall (0 : E2) rho ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hbound : ∀ x ∈ closedBall (0 : E2) rho,
      ‖x‖ ^ 2 ≤ g x ∧ g x ≤ rho ^ 2)
    (hseam : ∀ x ∈ closedBall (0 : E2) rho,
      r0 ≤ ‖x‖ → g x = ‖x‖ ^ 2) :
    ∃ d : E2 → ℝ, ContDiff ℝ ∞ d ∧ HasCompactSupport d ∧
      tsupport d ⊆ closedBall (0 : E2) r0 ∧
      (∀ x ∈ closedBall (0 : E2) rho, d x = g x - ‖x‖ ^ 2) ∧
      (∀ x ∈ closedBall (0 : E2) rho,
        0 ≤ d x ∧ ‖x‖ ^ 2 + d x ≤ rho ^ 2) ∧
      ∀ x : E2, r0 < ‖x‖ → d x = 0 := by
  classical
  let d : E2 → ℝ := fun x => if ‖x‖ < rho then g x - ‖x‖ ^ 2 else 0
  have hzero (x : E2) (hx : r0 < ‖x‖) : d x = 0 := by
    dsimp only [d]
    split_ifs with h
    · rw [hseam x (mem_closedBall_zero_iff.mpr h.le) hx.le, sub_self]
    · rfl
  have hs : tsupport d ⊆ closedBall (0 : E2) r0 := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact mem_closedBall_self hr0.le
    by_contra h
    exact hx (hzero x (lt_of_not_ge (fun hle => h (mem_closedBall_zero_iff.mpr hle))))
  have hc : ContDiff ℝ ∞ d := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : ‖x‖ < rho
    · have hxU := hdiscU (mem_closedBall_zero_iff.mpr hx.le)
      apply ((hg.contDiffAt (hU.mem_nhds hxU)).sub
        (contDiff_norm_sq ℝ).contDiffAt).congr_of_eventuallyEq
      have hn : ∀ᶠ y : E2 in 𝓝 x, ‖y‖ < rho :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hx
      filter_upwards [hn] with y hy
      exact if_pos hy
    · have hx0 : r0 < ‖x‖ := hr0rho.trans_le (le_of_not_gt hx)
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E2 => (0 : ℝ)) x).congr_of_eventuallyEq
      have hn : ∀ᶠ y : E2 in 𝓝 x, r0 < ‖y‖ :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hx0
      filter_upwards [hn] with y hy
      exact hzero y hy
  have hformula (x : E2) (hx : x ∈ closedBall (0 : E2) rho) :
      d x = g x - ‖x‖ ^ 2 := by
    dsimp only [d]
    split_ifs with h
    · rfl
    · rw [hseam x hx (hr0rho.le.trans (le_of_not_gt h)), sub_self]
  refine ⟨d, hc, (isCompact_closedBall (0 : E2) r0).of_isClosed_subset
    (isClosed_tsupport d) hs, hs, hformula, ?_, hzero⟩
  intro x hx
  rw [hformula x hx]
  obtain ⟨hlo, hhi⟩ := hbound x hx
  constructor <;> linarith only [hlo, hhi]

theorem exists_stackMorseGraphShear
    (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hAi : ContDiffOn ℝ ∞ A.symm A.target)
    (c kappa rho r0 : ℝ) (hkappa : |kappa| = 1)
    (hr0 : 0 < r0) (hr0rho : r0 < rho)
    (hsource : closedBall (0 : E2) (2 * rho) ×ˢ
      Icc (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) ⊆ A.source)
    (d : E2 → ℝ) (hd : ContDiff ℝ ∞ d)
    (hsupport : tsupport d ⊆ closedBall (0 : E2) r0)
    (hbound : ∀ x ∈ closedBall (0 : E2) rho,
      0 ≤ d x ∧ ‖x‖ ^ 2 + d x ≤ rho ^ 2) :
    ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ C : Set E3,
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
        (∀ y, Phi 0 y = y) ∧
        (∀ x ∈ closedBall (0 : E2) rho, ∀ t ∈ Icc (0 : ℝ) 1,
          Phi t (A (x, c + kappa * ‖x‖ ^ 2)) =
            A (x, c + kappa * (‖x‖ ^ 2 + t * d x))) ∧
        IsCompact C ∧
        C ⊆ A '' (closedBall (0 : E2) r0 ×ˢ
          Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)) ∧
        (∀ t, tsupport (fun y => Phi t y - y) ⊆ C) ∧
        (∀ t, tsupport (fun y => (Phi t).symm y - y) ⊆ C) ∧
        ∀ t y, y ∉ C → Phi t y = y ∧ (Phi t).symm y = y := by
  classical
  have hrho : 0 < rho := hr0.trans hr0rho
  let gamma : ℝ → E2 → E2 × ℝ :=
    fun t x => (x, c + kappa * (‖x‖ ^ 2 + t * d x))
  let V : ℝ × (E2 × ℝ) → E2 × ℝ := fun p => (0, kappa * d p.2.1)
  let Q : Set (E2 × ℝ) := ball (0 : E2) (2 * rho) ×ˢ
    Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2)
  let U0 : Set (ℝ × (E2 × ℝ)) := univ ×ˢ Q
  let N : Set (E2 × ℝ) := {p | r0 < ‖p.1‖}
  let G : ℝ × E2 → ℝ × (E2 × ℝ) := fun p => (p.1, gamma p.1 p.2)
  let K := G '' (Icc (-1 : ℝ) 2 ×ˢ closedBall (0 : E2) rho)
  have hG : Continuous G := continuous_fst.prodMk
    (continuous_snd.prodMk (continuous_const.add (continuous_const.mul
      (((continuous_norm.comp continuous_snd).pow 2).add
        (continuous_fst.mul (hd.continuous.comp continuous_snd))))))
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E2) rho)).image hG
  have hQ : IsOpen Q := isOpen_ball.prod isOpen_Ioo
  have hU0 : IsOpen U0 := isOpen_univ.prod hQ
  have hQA : Q ⊆ A.source := by
    intro p hp
    exact hsource ⟨ball_subset_closedBall hp.1, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hgamma (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 2)
      (x : E2) (hx : x ∈ closedBall (0 : E2) rho) : gamma t x ∈ Q := by
    obtain ⟨hd0, hdb⟩ := hbound x hx
    have hl := mul_le_mul_of_nonneg_right ht.1 hd0
    have hu := mul_le_mul_of_nonneg_right ht.2 hd0
    have hlo : -(rho ^ 2) ≤ ‖x‖ ^ 2 + t * d x := by
      nlinarith only [hl, hdb, sq_nonneg ‖x‖]
    have hhi : ‖x‖ ^ 2 + t * d x ≤ 2 * rho ^ 2 := by
      nlinarith only [hu, hdb, sq_nonneg ‖x‖]
    have habs : |kappa * (‖x‖ ^ 2 + t * d x)| ≤ 2 * rho ^ 2 := by
      rw [abs_mul, hkappa, one_mul]
      exact abs_le.mpr ⟨by nlinarith only [hlo, sq_nonneg rho], hhi⟩
    have habs' := abs_le.mp habs
    have hxnorm := mem_closedBall_zero_iff.mp hx
    refine ⟨mem_ball_zero_iff.mpr (by linarith only [hxnorm, hrho]), ?_, ?_⟩
    · dsimp only [gamma]
      nlinarith only [habs'.1, sq_pos_of_pos hrho]
    · dsimp only [gamma]
      nlinarith only [habs'.2, sq_pos_of_pos hrho]
  have hKU : K ⊆ U0 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨mem_univ _, hgamma p.1 hp.1 p.2 hp.2⟩
  have hV : ContDiff ℝ ∞ V := contDiff_const.prodMk
    (contDiff_const.mul (hd.comp (contDiff_fst.comp contDiff_snd)))
  have hN : IsOpen N :=
    isOpen_lt continuous_const (continuous_fst.norm)
  have hzero (t : ℝ) (p : E2 × ℝ) (hp : p ∈ N) (_hpU : (t, p) ∈ U0) :
      V (t, p) = 0 := by
    have hz : d p.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact (not_lt_of_ge (mem_closedBall_zero_iff.mp (hsupport hs))) hp
    change (0, kappa * d p.1) = (0, 0)
    rw [hz, mul_zero]
  let gamma0 : ℝ → closedBall (0 : E2) rho → E2 × ℝ := fun t x => gamma t x
  have htracks (x : closedBall (0 : E2) rho) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
      (t, gamma0 t x) ∈ K := ⟨(t, x.1), ⟨⟨ht.1.le, ht.2.le⟩, x.2⟩, rfl⟩
  have hderiv (x : closedBall (0 : E2) rho) (t : ℝ)
      (_ht : t ∈ Ioo (-1 : ℝ) 2) :
      HasDerivAt (fun z => gamma0 z x) (V (t, gamma0 t x)) t := by
    have hlin := ((hasDerivAt_id t).mul_const (d x.1)).const_add (‖x.1‖ ^ 2)
    have hh := (hlin.const_mul kappa).const_add c
    simpa only [gamma0, gamma, V, one_mul, id_eq] using (hasDerivAt_const t x.1).prodMk hh
  obtain ⟨Xi, C0, hXi, hXii, hXi0, htrack, hC0, hC0sub, _hs, _hsi, hfix, _hfixN⟩ :=
    exists_ambient_evolution_of_localField_away hK hU0 hKU V hV.contDiffOn hN hzero
      gamma0 (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2) htracks hderiv
  have hC0Q : C0 ⊆ Q := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := (hC0sub hp).1
    exact heq ▸ hq.2
  have hC0A : C0 ⊆ A.source := hC0Q.trans hQA
  have hC0r : C0 ⊆ closedBall (0 : E2) r0 ×ˢ
      Ioo (c - 4 * rho ^ 2) (c + 4 * rho ^ 2) := by
    intro p hp
    exact ⟨mem_closedBall_zero_iff.mpr (le_of_not_gt (hC0sub hp).2), (hC0Q hp).2⟩
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := fun t =>
    chartConjugateDiffeomorph A hA hAi (Xi t) hC0 hC0A
      (fun x hx => (hfix t x hx).1)
  let C := A '' C0
  have hC : IsCompact C := hC0.image_of_continuousOn (A.continuousOn.mono hC0A)
  have hPhiFix (t : ℝ) (y : E3) (hy : y ∉ C) :
      Phi t y = y ∧ (Phi t).symm y = y := by
    exact ⟨chartConjugateMap_eq_self A (Xi t) (fun x hx => (hfix t x hx).1) hy,
      chartConjugateMap_eq_self A (Xi t).symm (fun x hx => (hfix t x hx).2) hy⟩
  refine ⟨Phi, C, ?_, ?_, ?_, ?_, hC, image_mono hC0r, ?_, ?_, hPhiFix⟩
  · exact chartConjugateMap_contDiff_family A hA hAi (fun t => Xi t) hXi
      (fun t => equiv_mapsTo_of_fixed_compl (Xi t).toEquiv
        (fun x hx => (hfix t x (fun h => hx (hC0A h))).1)) hC0 hC0A
      (fun t x hx => (hfix t x hx).1)
  · exact chartConjugateMap_contDiff_family A hA hAi (fun t => (Xi t).symm) hXii
      (fun t => equiv_mapsTo_of_fixed_compl (Xi t).symm.toEquiv
        (fun x hx => (hfix t x (fun h => hx (hC0A h))).2)) hC0 hC0A
      (fun t x hx => (hfix t x hx).2)
  · intro y
    change chartConjugateMap A (Xi 0) y = y
    by_cases hy : y ∈ A.target
    · rw [chartConjugateMap_of_mem A (Xi 0) hy, hXi0, A.right_inv hy]
    · simp only [chartConjugateMap, if_neg hy]
  · intro x hx t ht
    have hga : (x, c + kappa * ‖x‖ ^ 2) ∈ A.source := by
      simpa only [gamma, zero_mul, add_zero] using
        hQA (hgamma 0 (by norm_num) x hx)
    change chartConjugateMap A (Xi t) (A (x, c + kappa * ‖x‖ ^ 2)) = _
    rw [chartConjugateMap_apply_chart A (Xi t) hga]
    have ht' : t ∈ Ioo (-1 : ℝ) 2 := by constructor <;> linarith only [ht.1, ht.2]
    have he := htrack ⟨x, hx⟩ t ht'
    simp only [gamma0, gamma, zero_mul, add_zero] at he
    rw [he]
  · intro t
    apply closure_minimal _ hC.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hPhiFix t y hn).1)
  · intro t
    apply closure_minimal _ hC.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hPhiFix t y hn).2)

end PoincareConjecture.M25.Topology3D
