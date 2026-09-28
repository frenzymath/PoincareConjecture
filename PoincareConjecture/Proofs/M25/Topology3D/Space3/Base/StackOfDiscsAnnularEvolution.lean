import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartTimeField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.LocalFieldIsotopy
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FixedSphereBallPreservation











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "SP" => (ℝ × (ℝ × E2))


theorem exists_stackAnnularCutoff
    (g : P → E2) (A a b B δ : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B) (hδ : 0 < δ)
    (e : OpenPartialHomeomorph SP SP)
    (heq : (e : SP → SP) = stackAnnularInterpolation g)
    (hsource : e.source = Ioo (-2 : ℝ) 3 ×ˢ
      (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * δ}))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hfixed : ∀ z ∈ Ioo A B, ∀ q ∈ sphere (0 : E2) 1, g (z, q) = q) :
    ∃ ρ : SP → ℝ,
      let W : SP → P := fun p => ρ p • chartTimeField e p
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ e.target ∧
      (∀ᶠ p in 𝓝ˢ (e '' (Icc (-1 : ℝ) 2 ×ˢ
        (Icc a b ×ˢ {x : E2 | |‖x‖ - 1| ≤ δ}))), ρ p = 1) ∧
      (∀ p, ρ p ∈ Icc (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ e.target ∧
      (∀ p, (W p).1 = 0) ∧
      (∀ t z : ℝ, ∀ q : E2, ‖q‖ = 1 → W (t, (z, q)) = 0) ∧
      (∀ p ∈ tsupport ρ, p.1 ∈ Ioo (-2 : ℝ) 3 ∧ p.2.1 ∈ Ioo A B) := by
  let Q : Set E2 := {x : E2 | |‖x‖ - 1| ≤ δ}
  let C : Set SP := Icc (-1 : ℝ) 2 ×ˢ (Icc a b ×ˢ Q)
  have hQc : IsCompact Q := (isCompact_closedBall (0 : E2) (1 + δ)).of_isClosed_subset
    (isClosed_le (continuous_norm.sub continuous_const).abs continuous_const) (by
      intro x hx
      change |‖x‖ - 1| ≤ δ at hx
      apply mem_closedBall_zero_iff.mpr
      have h := (abs_le.mp hx).2
      linarith only [h])
  have hCc : IsCompact C := isCompact_Icc.prod (isCompact_Icc.prod hQc)
  have hCs : C ⊆ e.source := by
    rintro ⟨t, z, x⟩ ⟨ht, hz, hx⟩
    change |‖x‖ - 1| ≤ δ at hx
    have hheightBand : Icc a b ⊆ Ioo A B :=
      (Icc_subset_Ioo_iff hab.le).mpr ⟨hAa, hbB⟩
    rw [hsource]
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      hheightBand hz, by
        change |‖x‖ - 1| < 2 * δ
        linarith only [hx, hδ]⟩
  have hKc : IsCompact (e '' C) := hCc.image_of_continuousOn (e.continuousOn.mono hCs)
  have hKt : e '' C ⊆ e.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_source (hCs hp)
  obtain ⟨ρ, hρ, hρc, hρs, hnear, hrange⟩ :=
    exists_compact_smooth_cutoff hKc e.open_target hKt
  let W : SP → P := fun p => ρ p • chartTimeField e p
  have hW : ContDiff ℝ ∞ W := contDiff_cutoff_smul e.open_target ρ hρ hρs
    (chartTimeField e) (chartTimeField_contDiffOn e he hi)
  have hWc : HasCompactSupport W := hρc.smul_right
  have hWs : tsupport W ⊆ e.target := (tsupport_smul_subset_left ρ _).trans hρs
  have htime (p : SP) : (e p).1 = p.1 := by rw [heq]; rfl
  have hheight (p : SP) : (e p).2.1 = p.2.1 := by rw [heq]; rfl
  have hcoords (p : SP) (hp : p ∈ e.target) :
      p.1 ∈ Ioo (-2 : ℝ) 3 ∧ p.2.1 ∈ Ioo A B := by
    have hx := e.map_target hp
    rw [hsource] at hx
    have ht : (e.symm p).1 = p.1 :=
      (htime _).symm.trans (congrArg Prod.fst (e.right_inv hp))
    have hz : (e.symm p).2.1 = p.2.1 :=
      (hheight _).symm.trans (congrArg (fun v : SP => v.2.1) (e.right_inv hp))
    exact ⟨ht ▸ hx.1, hz ▸ hx.2.1⟩
  have hWh (p : SP) : (W p).1 = 0 := cutoff_smul_preserves_linear ρ hρs
    (chartTimeField e) (ContinuousLinearMap.fst ℝ ℝ E2)
    (fun y hy => chartTimeField_preserves_linear e he
      (ContinuousLinearMap.fst ℝ ℝ E2) (fun z _ => hheight z) y hy) p
  refine ⟨ρ, hρ, hρc, hρs, hnear, hrange, hW, hWc, hWs, hWh, ?_, ?_⟩
  · intro t z q hq
    by_cases hzero : ρ (t, (z, q)) = 0
    · simp only [hzero, zero_smul]
    · have htgt := hρs (subset_tsupport ρ hzero)
      have htz := hcoords (t, (z, q)) htgt
      have hfix (s : ℝ) : e (s, (z, q)) = (s, (z, q)) := by
        rw [heq]
        simp only [stackAnnularInterpolation,
          hfixed z htz.2 q (mem_sphere_zero_iff_norm.mpr hq),
          sub_self, smul_zero, add_zero]
      have hp : (t, (z, q)) ∈ e.source := by
        rw [hsource]
        refine ⟨htz.1, htz.2, ?_⟩
        change |‖q‖ - 1| < 2 * δ
        simpa only [hq, sub_self, abs_zero] using
          (show (0 : ℝ) < 2 * δ by linarith only [hδ])
      have hd : HasDerivAt (fun _ : ℝ => (z, q))
          (chartTimeField e (t, (z, q))) t := by
        simpa only [hfix, Prod.snd] using
          chartTimeField_track e he (fun p _ => htime p) t (z, q) hp
      have hv := hd.unique (hasDerivAt_const t (z, q))
      simp only [hv, smul_zero]
  · intro p hp
    exact hcoords p (hρs hp)


def stackPassiveHeightFiber
    (F : P ≃ₜ P) (hF : ∀ p : P, (F p).1 = p.1) (z : ℝ) : E2 ≃ₜ E2 where
  toFun := fun x => (F (z, x)).2
  invFun := fun y => (F.symm (z, y)).2
  left_inv := by
    intro x
    change (F.symm (z, (F (z, x)).2)).2 = x
    have hp : (z, (F (z, x)).2) = F (z, x) := Prod.ext (hF (z, x)).symm rfl
    rw [hp]
    exact congrArg Prod.snd (F.symm_apply_apply (z, x))
  right_inv := by
    intro y
    change (F (z, (F.symm (z, y)).2)).2 = y
    have hz : (F.symm (z, y)).1 = z := by
      have h := hF (F.symm (z, y))
      rw [F.apply_symm_apply] at h
      exact h.symm
    have hp : (z, (F.symm (z, y)).2) = F.symm (z, y) := Prod.ext hz.symm rfl
    rw [hp]
    exact congrArg Prod.snd (F.apply_symm_apply (z, y))
  continuous_toFun := (F.continuous.comp (continuous_const.prodMk continuous_id)).snd
  continuous_invFun := (F.symm.continuous.comp (continuous_const.prodMk continuous_id)).snd


theorem exists_stackAnnularEvolution
    (g : P → E2) (A a b B δ : ℝ)
    (hAa : A < a) (hab : a < b) (hbB : b < B) (hδ : 0 < δ)
    (e : OpenPartialHomeomorph SP SP)
    (heq : (e : SP → SP) = stackAnnularInterpolation g)
    (hsource : e.source = Ioo (-2 : ℝ) 3 ×ˢ
      (Ioo A B ×ˢ {x : E2 | |‖x‖ - 1| < 2 * δ}))
    (he : ContDiffOn ℝ ∞ e e.source) (ρ : SP → ℝ)
    (hnear : ∀ᶠ p in 𝓝ˢ (e '' (Icc (-1 : ℝ) 2 ×ˢ
      (Icc a b ×ˢ {x : E2 | |‖x‖ - 1| ≤ δ}))), ρ p = 1)
    (hW : ContDiff ℝ ∞ (fun p => ρ p • chartTimeField e p))
    (hWc : HasCompactSupport (fun p => ρ p • chartTimeField e p))
    (hWt : tsupport (fun p => ρ p • chartTimeField e p) ⊆ e.target)
    (hWh : ∀ p : SP, (ρ p • chartTimeField e p).1 = 0)
    (hWq : ∀ t z : ℝ, ∀ q : E2, ‖q‖ = 1 →
      ρ (t, (z, q)) • chartTimeField e (t, (z, q)) = 0) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞,
      ∃ H : ℝ → ℝ → (E2 ≃ₜ E2), ∃ S : Set P,
        S = Prod.snd '' tsupport (fun p => ρ p • chartTimeField e p) ∧
        IsCompact S ∧ S ⊆ Ioo A B ×ˢ (univ : Set E2) ∧
        ContDiff ℝ ∞ (fun p : SP => Φ p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : SP => (Φ p.1).symm p.2) ∧
        (∀ p : P, Φ 0 p = p) ∧
        (∀ t : ℝ, ∀ p : P,
          (Φ t p).1 = p.1 ∧ ((Φ t).symm p).1 = p.1) ∧
        (∀ t z : ℝ, ∀ x : E2,
          H t z x = (Φ t (z, x)).2 ∧
          (H t z).symm x = ((Φ t).symm (z, x)).2) ∧
        ContDiff ℝ ∞ (fun p : SP => H p.1 p.2.1 p.2.2) ∧
        ContDiff ℝ ∞ (fun p : SP => (H p.1 p.2.1).symm p.2.2) ∧
        (∀ t z : ℝ, ∀ q : E2, ‖q‖ = 1 →
          Φ t (z, q) = (z, q) ∧ H t z q = q ∧ (H t z).symm q = q) ∧
        (∀ t z : ℝ,
          H t z '' ball (0 : E2) 1 = ball 0 1 ∧
          H t z '' closedBall (0 : E2) 1 = closedBall 0 1 ∧
          (H t z).symm '' ball (0 : E2) 1 = ball 0 1 ∧
          (H t z).symm '' closedBall (0 : E2) 1 = closedBall 0 1) ∧
        (∀ t : ℝ,
          tsupport (fun p : P => Φ t p - p) ⊆ S ∧
          tsupport (fun p : P => (Φ t).symm p - p) ⊆ S) ∧
        (∀ t : ℝ, ∀ p : P, p ∉ S → Φ t p = p ∧ (Φ t).symm p = p) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ z ∈ Icc a b, ∀ x : E2,
          |‖x‖ - 1| ≤ δ →
          Φ t (z, x) = (z, x + Real.smoothTransition t • (g (z, x) - x))) ∧
        (∀ z ∈ Icc a b, ∀ x : E2, |‖x‖ - 1| ≤ δ → H 1 z x = g (z, x)) ∧
        (∀ (t : ℝ) (J : Set ℝ),
          Φ t '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
          Φ t '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 ∧
          (Φ t).symm '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
          (Φ t).symm '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1) := by
  let W : SP → P := fun p => ρ p • chartTimeField e p
  obtain ⟨k, l, hk, hl⟩ := clockField_bounds W hW hWc
  let Φ : ℝ → Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞ :=
    fun t => clockEvolutionDiffeomorph W hk hl hW hWc 0 t
  let S : Set P := Prod.snd '' tsupport W
  have hSc : IsCompact S := hWc.isCompact.image continuous_snd
  have htime (p : SP) : (e p).1 = p.1 := by rw [heq]; rfl
  have hheight (p : SP) : (e p).2.1 = p.2.1 := by rw [heq]; rfl
  have hSband : S ⊆ Ioo A B ×ˢ (univ : Set E2) := by
    rintro p ⟨v, hv, rfl⟩
    have ht := hWt hv
    have hx := e.map_target ht
    rw [hsource] at hx
    have hz : (e.symm v).2.1 = v.2.1 :=
      (hheight _).symm.trans (congrArg (fun q : SP => q.2.1) (e.right_inv ht))
    exact ⟨hz ▸ hx.2.1, mem_univ _⟩
  have hΦ : ContDiff ℝ ∞ (fun p : SP => Φ p.1 p.2) :=
    (clockEvolution_contDiff W hk hl hW hWc).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hΦi : ContDiff ℝ ∞ (fun p : SP => (Φ p.1).symm p.2) :=
    (clockEvolution_contDiff W hk hl hW hWc).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hzero (p : P) : Φ 0 p = p := clockEvolution_self W hk hl 0 p
  have hh (t : ℝ) (p : P) : (Φ t p).1 = p.1 ∧ ((Φ t).symm p).1 = p.1 :=
    ⟨clockEvolution_preserves_linear W hk hl (ContinuousLinearMap.fst ℝ ℝ E2)
      hWh 0 t p,
      clockEvolution_preserves_linear W hk hl (ContinuousLinearMap.fst ℝ ℝ E2)
        hWh t 0 p⟩
  let H : ℝ → ℝ → (E2 ≃ₜ E2) := fun t z =>
    stackPassiveHeightFiber (Φ t).toHomeomorph (fun p => (hh t p).1) z
  have hH : ContDiff ℝ ∞ (fun p : SP => H p.1 p.2.1 p.2.2) := hΦ.snd
  have hHi : ContDiff ℝ ∞ (fun p : SP => (H p.1 p.2.1).symm p.2.2) := hΦi.snd
  have hcircle (t z : ℝ) (q : E2) (hq : ‖q‖ = 1) :
      Φ t (z, q) = (z, q) ∧ H t z q = q ∧ (H t z).symm q = q := by
    have hf : Φ t (z, q) = (z, q) :=
      clockEvolution_eq_self W hk hl (z, q) (fun s => hWq s z q hq) 0 t
    have hi : (Φ t).symm (z, q) = (z, q) :=
      clockEvolution_eq_self W hk hl (z, q) (fun s => hWq s z q hq) t 0
    exact ⟨hf, congrArg Prod.snd hf, congrArg Prod.snd hi⟩
  have hballs (t z : ℝ) :
      H t z '' ball (0 : E2) 1 = ball 0 1 ∧
      H t z '' closedBall (0 : E2) 1 = closedBall 0 1 ∧
      (H t z).symm '' ball (0 : E2) 1 = ball 0 1 ∧
      (H t z).symm '' closedBall (0 : E2) 1 = closedBall 0 1 := by
    have hz0 (x : E2) : H 0 z x = x := congrArg Prod.snd (hzero (z, x))
    clear_value H Φ
    have hc (x : E2) : ContinuousOn (fun s : ℝ => H (s * t) z x) (Icc 0 1) := by
      have hp : Continuous (fun s : ℝ => (s * t, (z, x))) :=
        (continuous_id.mul continuous_const).prodMk continuous_const
      exact (hH.continuous.comp hp).continuousOn
    have hz (x : E2) : H (0 * t) z x = x := by
      simpa only [zero_mul] using hz0 x
    obtain ⟨ho, hclosed⟩ := fixedSphere_isotopy_image_balls (fun s => H (s * t) z)
      hc hz (fun s _ q hq => (hcircle (s * t) z q hq).2.1)
        (t := 1) (by norm_num)
    simp only [one_mul] at ho hclosed
    have hinverse (V : Set E2) (hV : H t z '' V = V) : (H t z).symm '' V = V := by
      calc
        _ = (H t z).symm '' (H t z '' V) := congrArg (fun Z => (H t z).symm '' Z) hV.symm
        _ = V := by
          rw [image_image]
          simpa only [(H t z).symm_apply_apply] using image_id' V
    exact ⟨ho, hclosed, hinverse _ ho, hinverse _ hclosed⟩
  have hsupport (t : ℝ) :
      tsupport (fun p : P => Φ t p - p) ⊆ S ∧
      tsupport (fun p : P => (Φ t).symm p - p) ⊆ S :=
    ⟨closure_minimal (clockEvolution_support_subset W hk hl 0 t) hSc.isClosed,
      closure_minimal (clockEvolution_support_subset W hk hl t 0) hSc.isClosed⟩
  have hout (t : ℝ) (p : P) (hp : p ∉ S) : Φ t p = p ∧ (Φ t).symm p = p := by
    have hv (s : ℝ) : W (s, p) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hp ⟨(s, p), hs, rfl⟩
    exact ⟨clockEvolution_eq_self W hk hl p hv 0 t,
      clockEvolution_eq_self W hk hl p hv t 0⟩
  have htrack (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) (z : ℝ) (hz : z ∈ Icc a b)
      (x : E2) (hx : |‖x‖ - 1| ≤ δ) :
      Φ t (z, x) = (z, x + Real.smoothTransition t • (g (z, x) - x)) := by
    let γ : ℝ → P := fun s => (e (s, (z, x))).2
    have hsrc (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) : (s, (z, x)) ∈ e.source := by
      have hheightBand : Icc a b ⊆ Ioo A B :=
        (Icc_subset_Ioo_iff hab.le).mpr ⟨hAa, hbB⟩
      rw [hsource]
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
        hheightBand hz, by
          change |‖x‖ - 1| < 2 * δ
          linarith only [hx, hδ]⟩
    have hγ0 : γ 0 = (z, x) := by
      simp only [γ, heq, stackAnnularInterpolation,
        Real.smoothTransition.zero_of_nonpos le_rfl, zero_smul, add_zero]
    have hγ (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 2) : HasDerivAt γ (W (s, γ s)) s := by
      have hmem : (s, γ s) ∈ e '' (Icc (-1 : ℝ) 2 ×ˢ
          (Icc a b ×ˢ {x : E2 | |‖x‖ - 1| ≤ δ})) :=
        ⟨(s, (z, x)), ⟨⟨hs.1.le, hs.2.le⟩, hz, hx⟩,
          Prod.ext (htime (s, (z, x))) rfl⟩
      have hρ : ρ (s, γ s) = 1 :=
        (eventually_nhdsSet_iff_forall.mp hnear _ hmem).self_of_nhds
      change HasDerivAt γ (ρ (s, γ s) • chartTimeField e (s, γ s)) s
      rw [hρ, one_smul]
      exact chartTimeField_track e he (fun p _ => htime p) s (z, x) (hsrc s hs)
    have htflow := clockEvolution_tracks W hk hl γ
      (a := -1) (b := 2) (s := 0) (by norm_num) hγ ht
    change clockEvolution W hk hl 0 t (γ 0) = γ t at htflow
    rw [hγ0] at htflow
    change clockEvolution W hk hl 0 t (z, x) = _
    simpa only [γ, heq, stackAnnularInterpolation, Prod.snd] using htflow
  have hend (z : ℝ) (hz : z ∈ Icc a b) (x : E2) (hx : |‖x‖ - 1| ≤ δ) :
      H 1 z x = g (z, x) := by
    change ((Φ 1) (z, x)).2 = g (z, x)
    have h := congrArg Prod.snd (htrack 1 (by norm_num) z hz x hx)
    simpa only [Real.smoothTransition.one_of_one_le le_rfl, one_smul,
      add_sub_cancel] using h
  have himage (F : P → P) (hF : ∀ p : P, (F p).1 = p.1) (V : Set E2)
      (hV : ∀ z : ℝ, (fun x : E2 => (F (z, x)).2) '' V = V) (J : Set ℝ) :
      F '' (J ×ˢ V) = J ×ˢ V := by
    ext y
    constructor
    · rintro ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩
      refine ⟨by simpa only [hF] using hz, ?_⟩
      rw [← hV z]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨hyz, hy⟩
      obtain ⟨x, hx, hxy⟩ := (show y.2 ∈ (fun x : E2 => (F (y.1, x)).2) '' V by
        rw [hV]; exact hy)
      exact ⟨(y.1, x), ⟨hyz, hx⟩, Prod.ext (hF (y.1, x)) hxy⟩
  have hproducts (t : ℝ) (J : Set ℝ) :
      Φ t '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
      Φ t '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 ∧
      (Φ t).symm '' (J ×ˢ ball (0 : E2) 1) = J ×ˢ ball 0 1 ∧
      (Φ t).symm '' (J ×ˢ closedBall (0 : E2) 1) = J ×ˢ closedBall 0 1 :=
    ⟨himage (Φ t) (fun p => (hh t p).1) _ (fun z => (hballs t z).1) J,
      himage (Φ t) (fun p => (hh t p).1) _ (fun z => (hballs t z).2.1) J,
      himage (Φ t).symm (fun p => (hh t p).2) _ (fun z => (hballs t z).2.2.1) J,
      himage (Φ t).symm (fun p => (hh t p).2) _ (fun z => (hballs t z).2.2.2) J⟩
  exact ⟨Φ, H, S, rfl, hSc, hSband, hΦ, hΦi, hzero, hh,
    (fun _ _ _ => ⟨rfl, rfl⟩), hH, hHi, hcircle, hballs,
    hsupport, hout, htrack, hend, hproducts⟩

end PoincareConjecture.M25.Topology3D
