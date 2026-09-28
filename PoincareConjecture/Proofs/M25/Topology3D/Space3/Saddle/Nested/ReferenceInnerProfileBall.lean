import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerProfileScaling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RoundProfileNativeModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace Pointwise

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_inner_reference_profile_ball_family :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    let H : ℝ := 17 / 16
    let delta : ℝ := 1 / 8192
    let B : ℝ := H + delta
    let Omega : Set E2 := {v : E2 | ‖v‖ < 1 / 2 ∧ U v < B}
    let C : E3 ≃L[ℝ] (E2 × ℝ) := heightCoordinates
    ∃ (vmin : E2) (m : ℝ) (e : OpenPartialHomeomorph E2 E2)
      (k : ℝ → ℝ),
      m = U vmin ∧ (63 : ℝ) / 64 ≤ m ∧ m ≤ 1 ∧ e 0 = vmin ∧
      e.source = Metric.ball 0 (Real.sqrt (B - m)) ∧
      e.target = Omega ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.source, U (e p) = m + ‖p‖ ^ 2) ∧
      (∀ b : ℝ, m ≤ b → b < B →
        e '' Metric.closedBall 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
        e '' Metric.ball 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v < b} ∧
        e '' Metric.sphere 0 (Real.sqrt (b - m)) =
          {v : E2 | v ∈ Q ∧ U v = b}) ∧
      ContDiff ℝ ∞ k ∧
      (∀ z : ℝ, k z ∈ Icc (H - 3 * delta / 4) (H + 3 * delta / 4)) ∧
      EqOn k id (Icc (H - delta / 2) (H + delta / 2)) ∧
      ∀ d : ℝ,
        let r : ℝ → ℝ := fun z => Real.sqrt (k (z - d) - m)
        ∃ T : OpenPartialHomeomorph (E2 × ℝ) E3,
          ContDiff ℝ ∞ r ∧
          (∀ z : ℝ, 0 < r z ∧ r z < Real.sqrt (B - m)) ∧
          (∀ p : E2 × ℝ, T p = C.symm (e (r p.2 • p.1), p.2)) ∧
          (∀ y : E3, T.symm y =
            ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)) ∧
          T.source = {p : E2 × ℝ | r p.2 • p.1 ∈ e.source} ∧
          T.target = {y : E3 | (C y).1 ∈ Omega} ∧
          ContDiffOn ℝ ∞ T T.source ∧
          ContDiffOn ℝ ∞ T.symm T.target ∧
          Metric.closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
          (∀ p : E2 × ℝ, (C (T p)).2 = p.2) ∧
          (∀ y : E3, (T.symm y).2 = (C y).2) ∧
          (∀ z : ℝ, z - d ∈ Icc (H - delta / 2) (H + delta / 2) →
            T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v ≤ z - d} ×ˢ ({z} : Set ℝ)) ∧
            T '' (Metric.ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v < z - d} ×ˢ ({z} : Set ℝ)) ∧
            T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
              C.symm '' ({v : E2 | v ∈ Q ∧ U v = z - d} ×ˢ ({z} : Set ℝ))) ∧
          let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
          let S : Set E3 := Set.range j
          let O : Set E3 := j '' {q : UnitTwoSphere |
            (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖}
          IsCompact O ∧
          ∀ (P : SurgeryCapProfile) (h tau lambda : ℝ),
            |h - H| ≤ delta / 4 → 0 < tau → 0 < lambda →
            lambda * P.heightBound < min (delta / 16) tau →
            let beta : ℝ := delta / 16
            let s : ℝ := h + d
            let E : Set E3 := (fun v : E2 => C.symm (v, U v + d)) ''
              {v : E2 | ‖v‖ < 1 / 2 ∧ U v ≤ h}
            let R : Set E3 := S ∩ {y : E3 | s ≤ (C y).2}
            let cap : UnitTwoSphere → E3 := fun q =>
              T ((P.model q).1, s + lambda * (P.model q).2)
            let north : Set E3 := cap '' {q : UnitTwoSphere | 0 ≤ (C (q : E3)).2}
            let south : Set E3 := cap '' {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0}
            let rim : Set E3 := T '' (Metric.sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
            let M := flatCapDiffeomorph P.horizontal P.vertical
              P.horizontal_smooth P.vertical_smooth
              (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
            ∃ (J : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
              (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (a : ℝ → ℝ)
              (A : BallNeighborhoodChart E3 E3),
              (∀ q : UnitTwoSphere,
                ((C (q : E3)).2 ≤ 0 →
                  J (q : E3) = (P.horizontal (C (q : E3)).2 • (C (q : E3)).1,
                    (C (q : E3)).2)) ∧
                (0 ≤ (C (q : E3)).2 → J (q : E3) = P.model q)) ∧
              (∀ t : ℝ, g t = h + lambda * t - (h - m - lambda) *
                (1 - Real.smoothTransition (2 * t + 3 / 2))) ∧
              StrictMono g ∧ g (-1) = m ∧ g 0 = h ∧
              (∀ t : ℝ, -1 / 4 ≤ t → g t = h + lambda * t) ∧
              ContDiff ℝ ∞ a ∧ (∀ t : ℝ, 0 < a t) ∧
              (∀ t : ℝ, -1 / 8 ≤ t → a t = Real.sqrt (g t - m)) ∧
              (∀ t ∈ Icc (-1 : ℝ) 0,
                a t ^ 2 * (P.horizontal t * Real.sqrt (1 - t ^ 2)) ^ 2 = g t - m) ∧
              A.chart.source = {y : E3 | a (J y).2 • (J y).1 ∈ e.source} ∧
              A.chart.target = {y : E3 | (C y).1 ∈ Omega} ∧
              (∀ y : E3, A.chart y =
                C.symm (e (a (J y).2 • (J y).1), g (J y).2 + d)) ∧
              (∀ y : E3, A.chart.symm y =
                J.symm ((a (g.symm ((C y).2 - d)))⁻¹ • e.symm (C y).1,
                  g.symm ((C y).2 - d))) ∧
              E ⊆ S ∩ {y : E3 | (C y).2 ≤ s} ∧
              S = E ∪ R ∪ O ∧
              A.boundary = E ∪ north ∧ E ∩ north = rim ∧
              (∀ b ∈ Icc (h - beta) h,
                A.inside ∩ {y : E3 | (C y).2 = b + d} =
                  T '' (Metric.ball (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
                A.closedRegion ∩ {y : E3 | (C y).2 = b + d} =
                  T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
                A.boundary ∩ {y : E3 | (C y).2 = b + d} =
                  T '' (Metric.sphere (0 : E2) 1 ×ˢ ({b + d} : Set ℝ))) ∧
              (∀ y ∈ A.closedRegion,
                ‖(C y).1‖ < 1 / 2 ∧ m + d ≤ (C y).2 ∧
                (C y).2 ≤ s + lambda * P.heightBound ∧
                U (C y).1 + d ≤ (C y).2) ∧
              (∀ y ∈ A.inside, ‖(C y).1‖ < 1 / 2 ∧ U (C y).1 + d < (C y).2) ∧
              (∀ q : UnitTwoSphere, -1 / 8 < (C (q : E3)).2 →
                A.chart (q : E3) = cap q) ∧
              Disjoint A.inside S ∧ Disjoint A.closedRegion O ∧
              A.closedRegion ∩ (R ∪ O) ⊆ north ∧
              ∃ N : BallNeighborhoodChart E3 E3,
                N.boundary = south ∪ north ∧
                N.chart.source = {y : E3 |
                  ((M (C y)).1, s + lambda * (M (C y)).2) ∈ T.source} ∧
                N.chart.target = T.target ∧
                (∀ y : E3, N.chart y =
                  T ((M (C y)).1, s + lambda * (M (C y)).2)) ∧
                (∀ y : E3, N.chart.symm y =
                  C.symm (M.symm ((T.symm y).1, ((T.symm y).2 - s) / lambda))) ∧
                N.closedRegion ⊆ A.closedRegion ∧
                N.closedRegion ⊆ {y : E3 | |(C y).2 - s| < tau} ∧
                north = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (C y).2} ∧
                south ∩ north = rim ∧
                (∀ q : UnitTwoSphere, -1 / 8 < (C (q : E3)).2 →
                  N.chart (q : E3) ∈ A.boundary) := by
  classical
  dsimp only
  let U : E2 → ℝ := fun v => ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  let H : ℝ := 17 / 16
  let delta : ℝ := 1 / 8192
  let B : ℝ := H + delta
  let Omega : Set E2 := {v | ‖v‖ < 1 / 2 ∧ U v < B}
  let C := heightCoordinates
  obtain ⟨vmin, m, e, k, hm, hmlo, hmhi, he0, hes, het, he, hei, heq,
    hefib, hk, hkr, hkid, hTube⟩ := exists_inner_reference_tube
  change e.source = ball 0 (Real.sqrt (B - m)) at hes
  change e.target = Omega at het
  change ∀ p ∈ e.source, U (e p) = m + ‖p‖ ^ 2 at heq
  change ∀ b : ℝ, m ≤ b → b < B →
    e '' closedBall 0 (Real.sqrt (b - m)) = {v | v ∈ Q ∧ U v ≤ b} ∧
    e '' ball 0 (Real.sqrt (b - m)) = {v | v ∈ Q ∧ U v < b} ∧
    e '' sphere 0 (Real.sqrt (b - m)) = {v | v ∈ Q ∧ U v = b} at hefib
  change EqOn k id (Icc (H - delta / 2) (H + delta / 2)) at hkid
  refine ⟨vmin, m, e, k, hm, hmlo, hmhi, he0, hes, het, he, hei, heq,
    hefib, hk, hkr, hkid, ?_⟩
  intro d
  let r : ℝ → ℝ := fun z => Real.sqrt (k (z - d) - m)
  obtain ⟨T, hr, hrb, hTf, hTi, hTs, hTt, hT, hTinv, hTc, hTh, hTih, hcuts⟩ := hTube d
  change ∀ z, 0 < r z ∧ r z < Real.sqrt (B - m) at hrb
  change ∀ p, T p = C.symm (e (r p.2 • p.1), p.2) at hTf
  change ∀ p, (C (T p)).2 = p.2 at hTh
  change T.target = {y : E3 | (C y).1 ∈ Omega} at hTt
  change ∀ z : ℝ, z - d ∈ Icc (H - delta / 2) (H + delta / 2) →
    T '' (closedBall 0 1 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ({v : E2 | v ∈ Q ∧ U v ≤ z - d} ×ˢ ({z} : Set ℝ)) ∧
    T '' (ball 0 1 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ({v : E2 | v ∈ Q ∧ U v < z - d} ×ˢ ({z} : Set ℝ)) ∧
    T '' (sphere 0 1 ×ˢ ({z} : Set ℝ)) =
      C.symm '' ({v : E2 | v ∈ Q ∧ U v = z - d} ×ˢ ({z} : Set ℝ)) at hcuts
  refine ⟨T, hr, hrb, hTf, hTi, hTs, hTt, hT, hTinv, hTc, hTh, hTih, hcuts, ?_⟩
  let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
  let S : Set E3 := range j
  let O : Set E3 := j '' {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖}
  have hjc : Continuous j := (nestedReferenceDiffeomorph d).continuous.comp continuous_subtype_val
  have hOc : IsCompact O := ((isClosed_le (C.continuous.comp continuous_subtype_val).snd
    continuous_const).union (isClosed_le continuous_const
      (C.continuous.comp continuous_subtype_val).fst.norm)).isCompact.image hjc
  refine ⟨hOc, ?_⟩
  intro P h tau lambda hh htau hlambda hsmall
  let beta : ℝ := delta / 16
  let s : ℝ := h + d
  let E : Set E3 := (fun v : E2 => C.symm (v, U v + d)) '' {v | ‖v‖ < 1 / 2 ∧ U v ≤ h}
  let R : Set E3 := S ∩ {y | s ≤ (C y).2}
  let cap : UnitTwoSphere → E3 := fun q => T ((P.model q).1, s + lambda * (P.model q).2)
  let north : Set E3 := cap '' {q | 0 ≤ (C (q : E3)).2}
  let south : Set E3 := cap '' {q | (C (q : E3)).2 ≤ 0}
  let rim : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
  have hM := P.one_le_heightBound
  have hsmallB : lambda * P.heightBound < beta := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hshort : lambda * P.heightBound < tau := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hlM : lambda ≤ lambda * P.heightBound := by nlinarith only [hlambda, hM]
  have hlB : lambda < beta := hlM.trans_lt hsmallB
  have hhw : H - delta / 4 ≤ h ∧ h ≤ H + delta / 4 := by
    constructor <;> linarith only [(abs_le.mp hh).1, (abs_le.mp hh).2]
  have hgap : lambda < h - m := by
    dsimp only [H, delta, beta] at hhw hlB
    linarith only [hmhi, hhw.1, hlB]
  have hupper : h + lambda * P.heightBound < B := by
    dsimp only [H, delta, beta, B] at hhw hsmallB ⊢
    linarith only [hhw.2, hsmallB]
  obtain ⟨J, hJhem, hJbound, hJopen, hJfiber⟩ := exists_round_profile_native_ball_model P
  change ∀ q : UnitTwoSphere,
    ((C (q : E3)).2 ≤ 0 → J q = (P.horizontal (C (q : E3)).2 • (C (q : E3)).1, (C (q : E3)).2)) ∧
    (0 ≤ (C (q : E3)).2 → J q = P.model q) at hJhem
  obtain ⟨g, a, hgf, hgm, hgm1, hg0, hgaff, ha, hap, hatop, hasq⟩ :=
    exists_inner_reference_profile_scaling P h m lambda hlambda hgap
  let rn : ℝ → ℝ := fun t => P.horizontal t * Real.sqrt (1 - t ^ 2)
  have hrn (t : ℝ) : 0 ≤ rn t := mul_nonneg (P.horizontal_pos t).le (Real.sqrt_nonneg _)
  have hapos (t : ℝ) (ht : -1 / 8 ≤ t) : 0 < g t - m := by
    have hm' := hgm (show (-1 : ℝ) < t by linarith)
    rw [hgm1] at hm'
    linarith
  have ha2 (t : ℝ) (ht : -1 / 8 ≤ t) : a t ^ 2 = g t - m := by
    rw [hatop t ht, Real.sq_sqrt (hapos t ht).le]
  have hns (c : ℝ) (x : E2) : ‖c • x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hdata (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      ‖a (J y).2 • (J y).1‖ ^ 2 ≤ g (J y).2 - m ∧
      m ≤ g (J y).2 ∧ g (J y).2 ≤ h + lambda * P.heightBound := by
    have hb := hJbound y hy
    have hlo := hgm.monotone hb.2.1
    have hhi := hgm.monotone hb.2.2
    rw [hgm1] at hlo
    rw [hgaff P.heightBound (by linarith)] at hhi
    refine ⟨?_, hlo, hhi⟩
    rw [hns]
    by_cases ht : (J y).2 ≤ 0
    · have hf : J y ∈ (J '' closedBall (0 : E3) 1) ∩ {p | p.2 = (J y).2} :=
        ⟨⟨y, hy, rfl⟩, rfl⟩
      rw [(hJfiber (J y).2 ⟨hb.2.1, ht⟩).2.1] at hf
      obtain ⟨x, hx, hex⟩ := hf
      have hn : ‖(J y).1‖ ≤ rn (J y).2 := by
        simpa only [← congrArg Prod.fst hex] using mem_closedBall_zero_iff.mp hx
      have he' := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (hrn _)).mpr hn) (sq_nonneg (a (J y).2))
      exact he'.trans_eq (hasq _ ⟨hb.2.1, ht⟩)
    · have hn : ‖(J y).1‖ ^ 2 ≤ 1 := by nlinarith only [hb.1, norm_nonneg (J y).1]
      have he' := mul_le_mul_of_nonneg_left hn (sq_nonneg (a (J y).2))
      simpa only [mul_one, ha2 (J y).2 (by linarith [lt_of_not_ge ht])] using he'
  have hbuffer (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      a (J y).2 • (J y).1 ∈ e.source := by
    rw [hes, mem_ball_zero_iff]
    have hb := hdata y hy
    have hBm : 0 ≤ B - m := by linarith only [hb.2.1, hb.2.2, hupper]
    have hsqrt := Real.sq_sqrt hBm
    have hnonneg := Real.sqrt_nonneg (B - m)
    nlinarith only [hb.1, hb.2.2, hupper, hsqrt, hnonneg, norm_nonneg (a (J y).2 • (J y).1)]
  let Wsource : Set (E2 × ℝ) := {p | a p.2 • p.1 ∈ e.source}
  let Wtarget : Set E3 := {y | (C y).1 ∈ Omega}
  let f : E2 × ℝ → E3 := fun p => C.symm (e (a p.2 • p.1), g p.2 + d)
  let v : E3 → ℝ := fun y => g.symm ((C y).2 - d)
  let fi : E3 → E2 × ℝ := fun y => ((a (v y))⁻¹ • e.symm (C y).1, v y)
  have hscale : ContDiff ℝ ∞ (fun p : E2 × ℝ => a p.2 • p.1) :=
    (ha.comp contDiff_snd).smul contDiff_fst
  have hv : ContDiff ℝ ∞ v := g.symm.contDiff.comp (C.contDiff.snd.sub contDiff_const)
  have hai : ContDiff ℝ ∞ (fun y : E3 => (a (v y))⁻¹) := (ha.comp hv).inv (fun y => (hap _).ne')
  have hf : ContDiffOn ℝ ∞ f Wsource := C.symm.contDiff.comp_contDiffOn
    ((he.comp hscale.contDiffOn (fun _ hp => hp)).prodMk
      ((g.contDiff.comp contDiff_snd).add contDiff_const).contDiffOn)
  have hfi : ContDiffOn ℝ ∞ fi Wtarget := (hai.contDiffOn.smul
    (hei.comp C.contDiff.fst.contDiffOn (fun _ hy => het.symm ▸ hy))).prodMk hv.contDiffOn
  have hmapf (p : E2 × ℝ) (hp : p ∈ Wsource) : f p ∈ Wtarget := by
    change (C (C.symm (e (a p.2 • p.1), g p.2 + d))).1 ∈ Omega
    rw [C.apply_symm_apply, ← het]
    exact e.map_source hp
  have hmapfi (y : E3) (hy : y ∈ Wtarget) : fi y ∈ Wsource := by
    change a (v y) • ((a (v y))⁻¹ • e.symm (C y).1) ∈ e.source
    rw [smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul]
    exact e.map_target (het.symm ▸ hy)
  have hif (p : E2 × ℝ) (hp : p ∈ Wsource) : fi (f p) = p := by
    have hvf : v (f p) = p.2 := by
      dsimp only [v, f]; rw [C.apply_symm_apply, add_sub_cancel_right, g.symm_apply_apply]
    dsimp only [fi]
    rw [hvf]
    dsimp only [f]
    rw [C.apply_symm_apply, e.left_inv hp, smul_smul, inv_mul_cancel₀ (hap _).ne', one_smul]
  have hff (y : E3) (hy : y ∈ Wtarget) : f (fi y) = y := by
    dsimp only [f, fi]
    rw [smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul, e.right_inv (het.symm ▸ hy)]
    dsimp only [v]
    rw [g.apply_symm_apply, sub_add_cancel, Prod.eta, C.symm_apply_apply]
  let W : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    { toFun := f, invFun := fi, source := Wsource, target := Wtarget
      map_source' := hmapf, map_target' := hmapfi, left_inv' := hif, right_inv' := hff
      open_source := e.open_source.preimage hscale.continuous
      open_target := (het ▸ e.open_target).preimage C.continuous.fst
      continuousOn_toFun := hf.continuousOn, continuousOn_invFun := hfi.continuousOn }
  let A : BallNeighborhoodChart E3 E3 :=
    { chart := J.toHomeomorph.toOpenPartialHomeomorph.trans W
      closedBall_subset_source := fun y hy => ⟨mem_univ _, hbuffer y hy⟩
      smooth := hf.comp J.contDiff.contDiffOn (fun _ hy => hy.2)
      smooth_symm := J.symm.contDiff.comp_contDiffOn (hfi.mono inter_subset_left) }
  have hAs : A.chart.source = {y : E3 | a (J y).2 • (J y).1 ∈ e.source} := by
    ext y
    change (y ∈ (univ : Set E3) ∧ a (J y).2 • (J y).1 ∈ e.source) ↔ _
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hAt : A.chart.target = {y : E3 | (C y).1 ∈ Omega} := by
    ext y
    change ((C y).1 ∈ Omega ∧ fi y ∈ (univ : Set (E2 × ℝ))) ↔ _
    simp only [mem_univ, and_true, mem_ofPred_eq]
  have hAf (y : E3) : A.chart y = C.symm (e (a (J y).2 • (J y).1), g (J y).2 + d) := rfl
  have hAi (y : E3) : A.chart.symm y =
      J.symm ((a (g.symm ((C y).2 - d)))⁻¹ • e.symm (C y).1, g.symm ((C y).2 - d)) := rfl
  have hAh (y : E3) : (C (A.chart y)).2 = g (J y).2 + d := by rw [hAf, C.apply_symm_apply]
  have hAp (y : E3) : (C (A.chart y)).1 = e (a (J y).2 • (J y).1) := by rw [hAf, C.apply_symm_apply]
  have hsolid (y : E3) (hy : y ∈ A.closedRegion) :
      ‖(C y).1‖ < 1 / 2 ∧ m + d ≤ (C y).2 ∧ (C y).2 ≤ s + lambda * P.heightBound ∧
      U (C y).1 + d ≤ (C y).2 := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hb := hbuffer x hx
    have ht : e (a (J x).2 • (J x).1) ∈ Omega := het ▸ e.map_source hb
    have hd := hdata x hx
    rw [hAp, hAh]
    refine ⟨ht.1, by linarith only [hd.2.1], by dsimp only [s]; linarith only [hd.2.2], ?_⟩
    rw [heq _ hb]
    linarith only [hd.1]
  have hopen (y : E3) (hy : y ∈ A.inside) :
      ‖(C y).1‖ < 1 / 2 ∧ U (C y).1 + d < (C y).2 := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hxc := ball_subset_closedBall hx
    have hb := hbuffer x hxc
    have hd := hJbound x hxc
    have ht : e (a (J x).2 • (J x).1) ∈ Omega := het ▸ e.map_source hb
    rw [hAp, hAh]
    refine ⟨ht.1, ?_⟩
    rw [heq _ hb, hns]
    by_cases hz : (J x).2 ≤ 0
    · have hmem : J x ∈ (J '' ball (0 : E3) 1) ∩ {p | p.2 = (J x).2} :=
        ⟨⟨x, hx, rfl⟩, rfl⟩
      rw [(hJfiber (J x).2 ⟨hd.2.1, hz⟩).1] at hmem
      obtain ⟨w, hw, hew⟩ := hmem
      have hn : ‖(J x).1‖ < rn (J x).2 := by
        simpa only [← congrArg Prod.fst hew] using mem_ball_zero_iff.mp hw
      have he' := mul_lt_mul_of_pos_left
        ((sq_lt_sq₀ (norm_nonneg _) (hrn _)).mpr hn) (sq_pos_of_pos (hap (J x).2))
      rw [hasq _ ⟨hd.2.1, hz⟩] at he'
      linarith only [he']
    · have hn := hJopen x hx
      have hs : ‖(J x).1‖ ^ 2 < 1 := by nlinarith only [hn, norm_nonneg (J x).1]
      have he' := mul_lt_mul_of_pos_left hs (sq_pos_of_pos (hap (J x).2))
      rw [mul_one, ha2 _ (by linarith [lt_of_not_ge hz])] at he'
      rw [ha2 (J x).2 (by linarith [lt_of_not_ge hz])]
      linarith only [he']
  have hpatch (q : UnitTwoSphere) (hq : -1 / 8 < (C (q : E3)).2) : A.chart q = cap q := by
    have hj : J (q : E3) = P.model q := by
      by_cases hp : 0 ≤ (C (q : E3)).2
      · exact (hJhem q).2 hp
      · have hn : (C (q : E3)).2 < 0 := lt_of_not_ge hp
        have hc := surgeryCapModel_cylinder P.horizontal P.vertical P.horizontal_smooth
          P.vertical_smooth (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
          P.horizontal_near P.vertical_far q (abs_le.mpr ⟨by linarith, by linarith⟩)
        change P.model q = ((circleDirection (C (q : E3)).1 : E2), (C (q : E3)).2) at hc
        rw [(hJhem q).1 hn.le]
        apply Prod.ext
        · rfl
        · change (C (q : E3)).2 = (P.model q).2
          rw [hc]
    have htlo : -1 / 8 < (P.model q).2 := by
      by_cases hp : 0 ≤ (C (q : E3)).2
      · have h0 : 0 ≤ (P.model q).2 := mul_nonneg (P.vertical_pos _).le hp
        linarith only [h0]
      · have hj' := (hJhem q).1 (le_of_not_ge hp)
        have hs := congrArg Prod.snd (hj.symm.trans hj')
        exact hs.symm ▸ hq
    have hthi : (P.model q).2 ≤ P.heightBound := (abs_le.mp (P.height_bound q)).2
    have hcenter : g (P.model q).2 ∈ Icc (H - delta / 2) (H + delta / 2) := by
      rw [hgaff _ (by linarith only [htlo])]
      have hlo := mul_lt_mul_of_pos_left htlo hlambda
      have hhi := mul_le_mul_of_nonneg_left hthi hlambda.le
      constructor <;> dsimp only [H, delta, beta] at hhw hlB hsmallB ⊢ <;>
        linarith only [hhw.1, hhw.2, hlB, hsmallB, hlo, hhi]
    have har : a (P.model q).2 = r (g (P.model q).2 + d) := by
      rw [hatop _ htlo.le]
      dsimp only [r]
      rw [add_sub_cancel_right, hkid hcenter]
      rfl
    rw [hAf, hj]
    change C.symm (e (a (P.model q).2 • (P.model q).1), g (P.model q).2 + d) = T _
    have hz : s + lambda * (P.model q).2 = g (P.model q).2 + d := by
      rw [hgaff _ (by linarith only [htlo])]; dsimp only [s]; ring
    rw [hTf]
    change C.symm (e (a (P.model q).2 • (P.model q).1), g (P.model q).2 + d) =
      C.symm (e (r (s + lambda * (P.model q).2) • (P.model q).1), s + lambda * (P.model q).2)
    rw [hz, har]
  have hlower (q : UnitTwoSphere) (hq : (C (q : E3)).2 ≤ 0) : A.chart q ∈ E := by
    have hj := (hJhem q).1 hq
    have hb := hJbound q (sphere_subset_closedBall q.property)
    have ht : (J (q : E3)).2 ∈ Icc (-1 : ℝ) 0 := ⟨hb.2.1, by rw [hj]; exact hq⟩
    have hfib : J (q : E3) ∈ (J '' sphere (0 : E3) 1) ∩ {p | p.2 = (J (q : E3)).2} :=
      ⟨⟨q, q.property, rfl⟩, rfl⟩
    rw [(hJfiber _ ht).2.2] at hfib
    obtain ⟨x, hx, hex⟩ := hfib
    have hnorm : ‖(J (q : E3)).1‖ = rn (J (q : E3)).2 := by
      simpa only [← congrArg Prod.fst hex] using mem_sphere_zero_iff_norm.mp hx
    have hbuf := hbuffer q (sphere_subset_closedBall q.property)
    have him : e (a (J (q : E3)).2 • (J (q : E3)).1) ∈ Omega := het ▸ e.map_source hbuf
    have hu : U (e (a (J (q : E3)).2 • (J (q : E3)).1)) = g (J (q : E3)).2 := by
      rw [heq _ hbuf, hns, hnorm, hasq _ ht]; ring
    refine ⟨e (a (J (q : E3)).2 • (J (q : E3)).1), ⟨him.1, ?_⟩, ?_⟩
    · rw [hu, ← hg0]; exact hgm.monotone ht.2
    · change C.symm (_, U _ + d) = A.chart q
      rw [hu, hAf]
  have hback (y : E3) (hy : y ∈ E) : y ∈ A.boundary := by
    obtain ⟨w, hw, rfl⟩ := hy
    have hwt : w ∈ e.target := het.symm ▸ ⟨hw.1, hw.2.trans_lt (by linarith [hupper, hlambda, hM])⟩
    let p := e.symm w
    have hps : p ∈ e.source := e.map_target hwt
    have hpw : e p = w := e.right_inv hwt
    have hu : U w = m + ‖p‖ ^ 2 := by rw [← hpw, heq _ hps]
    let t := g.symm (U w)
    have hgt : g t = U w := g.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hgm.le_iff_le.mp
      · rw [hgm1, hgt, hu]; exact le_add_of_nonneg_right (sq_nonneg _)
      · rw [hgt, hg0]; exact hw.2
    let x := (a t)⁻¹ • p
    have hxp : a t • x = p := by dsimp [x]; rw [smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul]
    have hxn : ‖x‖ = rn t := by
      have hs : ‖x‖ ^ 2 = rn t ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 (hap t).ne')
        rw [← hns, hxp, hasq _ ht, hgt, hu]; ring
      exact (sq_eq_sq₀ (norm_nonneg _) (hrn _)).mp hs
    have hfib : (x, t) ∈ (J '' sphere (0 : E3) 1) ∩ {p | p.2 = t} := by
      rw [(hJfiber t ht).2.2]
      exact ⟨x, mem_sphere_zero_iff_norm.mpr hxn, rfl⟩
    obtain ⟨v', hv', hj⟩ := hfib.1
    refine ⟨v', hv', ?_⟩
    rw [hAf, hj, hxp, hpw, hgt]
  have hboundary : A.boundary = E ∪ north := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hh' : (C w).2 ≤ 0
      · exact Or.inl (hlower ⟨w, hw⟩ hh')
      · exact Or.inr ⟨⟨w, hw⟩, (lt_of_not_ge hh').le,
          (hpatch ⟨w, hw⟩ (by linarith [lt_of_not_ge hh'])).symm⟩
    · rintro (hy | ⟨q, hq, rfl⟩)
      · exact hback y hy
      · change 0 ≤ (C (q : E3)).2 at hq
        exact ⟨q, q.property, hpatch q (by linarith only [hq])⟩
  have imageFiber (K : Set E3) (D0 : Set E2) (t : ℝ)
      (hfib : (J '' K) ∩ {p | p.2 = t} = (fun x : E2 => (x, t)) '' D0) :
      (A.chart '' K) ∩ {y | (C y).2 = g t + d} =
        (fun x : E2 => C.symm (e (a t • x), g t + d)) '' D0 := by
    ext y; constructor
    · rintro ⟨⟨w, hw, rfl⟩, hh'⟩
      change (C (A.chart w)).2 = g t + d at hh'
      have ht : (J w).2 = t := hgm.injective (by
        rw [hAh] at hh'; exact add_right_cancel hh')
      have hf' : J w ∈ (J '' K) ∩ {p | p.2 = t} := ⟨⟨w, hw, rfl⟩, ht⟩
      rw [hfib] at hf'
      obtain ⟨x, hx, he'⟩ := hf'
      exact ⟨x, hx, by rw [hAf, ← he']⟩
    · rintro ⟨x, hx, rfl⟩
      have hf' : (x, t) ∈ (J '' K) ∩ {p | p.2 = t} := by rw [hfib]; exact ⟨x, hx, rfl⟩
      obtain ⟨w, hw, he'⟩ := hf'.1
      exact ⟨⟨w, hw, by rw [hAf, he']⟩, by
        change (C (C.symm (e (a t • x), g t + d))).2 = _
        rw [C.apply_symm_apply]⟩
  have hCuts (b : ℝ) (hb : b ∈ Icc (h - beta) h) :
      A.inside ∩ {y | (C y).2 = b + d} = T '' (ball (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
      A.closedRegion ∩ {y | (C y).2 = b + d} = T '' (closedBall (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
      A.boundary ∩ {y | (C y).2 = b + d} = T '' (sphere (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) := by
    have hmb : m < b := by dsimp only [H, delta, beta] at hhw hb; linarith only [hmhi, hhw.1, hb.1]
    have hbc : b ∈ Icc (H - delta / 2) (H + delta / 2) := by
      dsimp only [H, delta, beta] at hhw hb ⊢
      constructor <;> linarith only [hhw.1, hhw.2, hb.1, hb.2]
    let t := g.symm b
    have hgt : g t = b := g.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hgm.le_iff_le.mp
      · rw [hgm1, hgt]; exact hmb.le
      · rw [hgt, hg0]; exact hb.2
    have htm : -1 < t := hgm.lt_iff_lt.mp (by rw [hgm1, hgt]; exact hmb)
    have hrnp : 0 < rn t := mul_pos (P.horizontal_pos t) (Real.sqrt_pos.mpr (by
      have hh' := mul_pos (show 0 < 1 - t by linarith only [ht.2]) (show 0 < 1 + t by linarith)
      nlinarith only [hh']))
    have hrz : r (b + d) = Real.sqrt (b - m) := by
      dsimp only [r]; rw [add_sub_cancel_right, hkid hbc]
      rfl
    have hprod : a t * rn t = r (b + d) := by
      apply (sq_eq_sq₀ (mul_pos (hap t) hrnp).le (hrb (b + d)).1.le).mp
      rw [mul_pow, hasq t ht, hgt, hrz, Real.sq_sqrt (sub_pos.mpr hmb).le]
    have hscale (D0 : Set E2) :
        (fun x : E2 => C.symm (e (a t • x), b + d)) '' ((fun x : E2 => rn t • x) '' D0) =
          T '' (D0 ×ˢ ({b + d} : Set ℝ)) := by
      rw [image_image]
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨(x, b + d), ⟨hx, rfl⟩, ?_⟩
        rw [hTf]
        change C.symm (e (r (b + d) • x), b + d) = C.symm (e (a t • (rn t • x)), b + d)
        rw [smul_smul, hprod]
      · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
        have hz' : z = b + d := hz
        subst z
        refine ⟨x, hx, ?_⟩
        rw [hTf]
        change C.symm (e (a t • (rn t • x)), b + d) = C.symm (e (r (b + d) • x), b + d)
        rw [smul_smul, hprod]
    have hbo : (fun x : E2 => rn t • x) '' ball (0 : E2) 1 = ball 0 (rn t) := by
      rw [image_smul, smul_unitBall_of_pos hrnp]
    have hbc' : (fun x : E2 => rn t • x) '' closedBall (0 : E2) 1 = closedBall 0 (rn t) := by
      rw [image_smul, smul_unitClosedBall_of_nonneg hrnp.le]
    have hbs : (fun x : E2 => rn t • x) '' sphere (0 : E2) 1 = sphere 0 (rn t) := by
      rw [image_smul, smul_sphere' hrnp.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hrnp, mul_one]
    have ho := imageFiber (ball (0 : E3) 1) (ball (0 : E2) (rn t)) t (hJfiber t ht).1
    have hc := imageFiber (closedBall (0 : E3) 1) (closedBall (0 : E2) (rn t)) t (hJfiber t ht).2.1
    have hs := imageFiber (sphere (0 : E3) 1) (sphere (0 : E2) (rn t)) t (hJfiber t ht).2.2
    rw [hgt, ← hbo, hscale] at ho
    rw [hgt, ← hbc', hscale] at hc
    rw [hgt, ← hbs, hscale] at hs
    exact ⟨ho, hc, hs⟩
  have hEheight (y : E3) (hy : y ∈ E) : (C y).2 ≤ s := by
    obtain ⟨w, hw, rfl⟩ := hy
    rw [C.apply_symm_apply]
    dsimp only [s]; linarith only [hw.2]
  have hNorthHeight (y : E3) (hy : y ∈ north) : s ≤ (C y).2 := by
    obtain ⟨q, hq, rfl⟩ := hy
    change s ≤ (C (T _)).2
    rw [hTh]
    have h0 : 0 ≤ (P.model q).2 := mul_nonneg (P.vertical_pos _).le hq
    nlinarith only [hlambda, h0]
  have hrimE : rim ⊆ E := by
    intro y hy
    change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) at hy
    have hyt : y ∈ T.target := by
      obtain ⟨p, hp, rfl⟩ := hy
      exact T.map_source (hTc ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)
    rw [hTt] at hyt
    have hc := (hcuts s (by
      change h + d - d ∈ Icc (H - delta / 2) (H + delta / 2)
      rw [add_sub_cancel_right]
      constructor <;> dsimp only [H, delta] at hhw ⊢ <;> linarith only [hhw.1, hhw.2])).2.2
    change T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) = _ at hc
    rw [hc] at hy
    obtain ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩ := hy
    have hz' : z = s := hz
    subst z
    have huw : U w = h := by simpa only [s, add_sub_cancel_right] using hw.2
    change (C (C.symm (w, s))).1 ∈ Omega at hyt
    rw [C.apply_symm_apply] at hyt
    refine ⟨w, ⟨hyt.1, huw.le⟩, ?_⟩
    change C.symm (w, U w + d) = C.symm (w, s)
    rw [huw]
  have hrimNorth : rim ⊆ north := by
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    have hz' : z = s := hz
    subst z
    have hn : ‖C.symm (x, (0 : ℝ))‖ = 1 := by
      have hs := heightCoordinates_symm_norm_sq (x, (0 : ℝ))
      rw [mem_sphere_zero_iff_norm.mp hx] at hs
      nlinarith only [hs, norm_nonneg (C.symm (x, (0 : ℝ)))]
    let q : UnitTwoSphere := ⟨C.symm (x, 0), mem_sphere_zero_iff_norm.mpr hn⟩
    have hq : C (q : E3) = (x, 0) := C.apply_symm_apply _
    have hp0 : P.horizontal 0 = 1 := by simpa using P.horizontal_near 0 (by norm_num)
    have hmodel : P.model q = (x, 0) := by
      have he' := ((hJhem q).2 (by rw [hq])).symm.trans ((hJhem q).1 (by rw [hq]))
      simpa only [hq, hp0, one_smul] using he'
    refine ⟨q, by change 0 ≤ (C (q : E3)).2; rw [hq], ?_⟩
    change T ((P.model q).1, s + lambda * (P.model q).2) = T (x, s)
    rw [hmodel, mul_zero, add_zero]
  have hmeet : E ∩ north = rim := by
    apply subset_antisymm
    · rintro y ⟨hyE, hyN⟩
      have hyh : (C y).2 = s := le_antisymm (hEheight y hyE) (hNorthHeight y hyN)
      change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ))
      rw [← (hCuts h ⟨by dsimp [beta, delta]; linarith, le_rfl⟩).2.2]
      exact ⟨hboundary.symm ▸ Or.inl hyE, hyh⟩
    · exact fun y hy => ⟨hrimE hy, hrimNorth hy⟩
  have hjp (q : UnitTwoSphere) : (C (j q)).1 = (C (q : E3)).1 := by
    ext i
    fin_cases i <;> rfl
  have hjh (q : UnitTwoSphere) : (C (j q)).2 =
      (C (q : E3)).2 + ‖(C (q : E3)).1‖ ^ 2 + (C (q : E3)).1 0 / 32 + d := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (q : E3) 2 + (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 0 / 32 + d =
      (q : E3) 2 + ((q : E3) 0 ^ 2 + (q : E3) 1 ^ 2) + (q : E3) 0 / 32 + d
    ring
  have hjupper (q : UnitTwoSphere) : (C (j q)).2 ≤ U (C (q : E3)).1 + d := by
    have hs := sphere_height_coordinates_sq q
    have hrad : 0 ≤ 1 - ‖(C (q : E3)).1‖ ^ 2 := by nlinarith only [hs, sq_nonneg (C (q : E3)).2]
    have he' := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 - ‖(C (q : E3)).1‖ ^ 2)
    rw [hjh]
    dsimp only [U]
    nlinarith only [hs, he', hn]
  have hjpositive (q : UnitTwoSphere) (hq : 0 ≤ (C (q : E3)).2) :
      (C (j q)).2 = U (C (q : E3)).1 + d := by
    have hs := sphere_height_coordinates_sq q
    have hrad : 0 ≤ 1 - ‖(C (q : E3)).1‖ ^ 2 := by nlinarith only [hs, sq_nonneg (C (q : E3)).2]
    have he' := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (1 - ‖(C (q : E3)).1‖ ^ 2)
    rw [hjh]
    dsimp only [U]
    have hh' : (C (q : E3)).2 = Real.sqrt (1 - ‖(C (q : E3)).1‖ ^ 2) := by
      nlinarith only [hs, he', hn, hq]
    rw [hh']; ring
  have hES : E ⊆ S ∩ {y | (C y).2 ≤ s} := by
    intro y hy
    refine ⟨?_, hEheight y hy⟩
    obtain ⟨w, hw, rfl⟩ := hy
    have hrad : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith only [hw.1, norm_nonneg w]
    have hn : ‖C.symm (w, Real.sqrt (1 - ‖w‖ ^ 2))‖ = 1 := by
      have hs := heightCoordinates_symm_norm_sq (w, Real.sqrt (1 - ‖w‖ ^ 2))
      rw [Real.sq_sqrt hrad] at hs
      nlinarith only [hs, norm_nonneg (C.symm (w, Real.sqrt (1 - ‖w‖ ^ 2)))]
    let q : UnitTwoSphere := ⟨C.symm (w, Real.sqrt (1 - ‖w‖ ^ 2)), mem_sphere_zero_iff_norm.mpr hn⟩
    have hq : C (q : E3) = (w, Real.sqrt (1 - ‖w‖ ^ 2)) := C.apply_symm_apply _
    refine ⟨q, C.injective (Prod.ext ?_ ?_)⟩
    · rw [hjp, hq, C.apply_symm_apply]
    · rw [hjpositive q (by rw [hq]; exact Real.sqrt_nonneg _), hq, C.apply_symm_apply]
  have hScover : S = E ∪ R ∪ O := by
    apply subset_antisymm
    · rintro y ⟨q, rfl⟩
      by_cases ho : (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖
      · exact Or.inr ⟨q, ho, rfl⟩
      · have hp : 0 < (C (q : E3)).2 := lt_of_not_ge (fun hh' => ho (Or.inl hh'))
        have hn : ‖(C (q : E3)).1‖ < 1 / 2 := lt_of_not_ge (fun hh' => ho (Or.inr hh'))
        by_cases hh' : (C (j q)).2 ≤ s
        · left; left
          refine ⟨(C (q : E3)).1, ⟨hn, ?_⟩, C.injective (Prod.ext ?_ ?_)⟩
          · rw [hjpositive q hp.le] at hh'; dsimp only [s] at hh'; linarith only [hh']
          · rw [C.apply_symm_apply, hjp]
          · rw [C.apply_symm_apply, hjpositive q hp.le]
        · exact Or.inl (Or.inr ⟨⟨q, rfl⟩, (lt_of_not_ge hh').le⟩)
    · rintro y ((hy | hy) | ⟨q, _hq, rfl⟩)
      · exact (hES hy).1
      · exact hy.1
      · exact ⟨q, rfl⟩
  have hdis : Disjoint A.inside S := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨q, rfl⟩
    have hi := (hopen (j q) hy).2
    rw [hjp] at hi
    linarith only [hi, hjupper q]
  have hdisO : Disjoint A.closedRegion O := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨q, hq, rfl⟩
    have hs := hsolid (j q) hy
    rw [hjp] at hs
    rcases hq with hq | hq
    · have hp : 0 < Real.sqrt (1 - ‖(C (q : E3)).1‖ ^ 2) := Real.sqrt_pos.mpr (by
        nlinarith only [hs.1, norm_nonneg (C (q : E3)).1])
      have hh' := hs.2.2.2
      rw [hjh] at hh'
      dsimp only [U] at hh'
      linarith only [hh', hp, hq]
    · exact (not_lt_of_ge hq) hs.1
  have havoid : A.closedRegion ∩ (R ∪ O) ⊆ north := by
    rintro y ⟨hy, hyR | hyO⟩
    · have hb : y ∈ A.boundary := by
        rw [← A.inside_union_boundary] at hy
        exact hy.resolve_left (fun hi => Set.disjoint_left.mp hdis hi hyR.1)
      rw [hboundary] at hb
      rcases hb with he' | hn
      · have heq' : (C y).2 = s := le_antisymm (hEheight y he') hyR.2
        have hr' : y ∈ rim := by
          change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ))
          rw [← (hCuts h ⟨by dsimp [beta, delta]; linarith, le_rfl⟩).2.2]
          exact ⟨hboundary.symm ▸ Or.inl he', heq'⟩
        exact hrimNorth hr'
      · exact hn
    · exact False.elim (Set.disjoint_left.mp hdisO hy hyO)
  have huNorm : ‖C.symm ((0 : E2), (1 : ℝ))‖ = 1 := by
    have hs := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, zero_add] at hs
    nlinarith only [hs, norm_nonneg (C.symm ((0 : E2), (1 : ℝ)))]
  let u : UnitTwoSphere := ⟨C.symm (0, 1), mem_sphere_zero_iff_norm.mpr huNorm⟩
  have hu (y : E3) : inner ℝ (u : E3) y = (C y).2 := by
    change inner ℝ (heightCoordinates.symm ((0 : E2), (1 : ℝ))) y = (heightCoordinates y).2
    simp only [heightCoordinates_symm_apply, EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, Fin.sum_univ_three, heightCoordinates_snd_apply]
    simp
  have hfilled (z : ℝ) (hz : z ∈ Icc (s - beta) s) :
      T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ⊆ A.closedRegion := by
    have hb : z - d ∈ Icc (h - beta) h := by
      dsimp only [s] at hz
      constructor <;> linarith only [hz.1, hz.2]
    have hc := (hCuts (z - d) hb).2.1
    rw [sub_add_cancel] at hc
    rw [← hc]
    exact inter_subset_left
  have hnorth : north ⊆ A.closedRegion := by
    intro y hy
    rw [← A.inside_union_boundary]
    exact Or.inr (hboundary.symm ▸ Or.inr hy)
  obtain ⟨N, hNb, hNs, hNt, hNf, hNi, hNc, hNh, hNnorth, hNmeet⟩ :=
    exists_saddle_contained_profile_ball P u T hTc hT hTinv
      (fun p _ => (hu (T p)).trans (hTh p)) A (s - beta) s lambda tau
      hlambda (by linarith only [hsmallB]) hshort hfilled hnorth
  have hNheight : N.closedRegion ⊆ {y : E3 | |(C y).2 - s| < tau} := by
    intro y hy
    have hh' := hNh hy
    change |inner ℝ (u : E3) y - s| < tau at hh'
    rwa [hu] at hh'
  refine ⟨J, g, a, A, hJhem, hgf, hgm, hgm1, hg0, hgaff, ha, hap, hatop, hasq,
    hAs, hAt, hAf, hAi, hES, hScover, hboundary, hmeet, hCuts, hsolid, hopen, hpatch,
    hdis, hdisO, havoid, N, hNb, hNs, hNt, hNf, hNi, hNc, hNheight, hNnorth, hNmeet, ?_⟩
  intro q hq
  rw [hNf]
  change cap q ∈ A.boundary
  rw [← hpatch q hq]
  exact ⟨q, q.property, rfl⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
