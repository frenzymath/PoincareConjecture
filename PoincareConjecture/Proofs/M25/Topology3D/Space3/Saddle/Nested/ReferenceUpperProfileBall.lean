import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceUpperTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerProfileScaling
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RoundProfileNativeModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceModel

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace Pointwise

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_upper_reference_profile_ball_family :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let L : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let C : E3 ≃L[ℝ] (E2 × ℝ) := heightCoordinates
    ∃ ws wm : ℝ,
      1 / 2 < ws ∧ ws < 3 / 4 ∧ g ws = 1 / 32 ∧
      0 < wm ∧ wm < 1 / 2 ∧ g wm = -(1 / 32) ∧
      let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
      let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
      let k : ℝ := U vs
      let mu : ℝ := U vm
      ∃ (rho : ℝ) (e0 e : OpenPartialHomeomorph E2 E2) (c : ℝ → ℝ),
        ‖vs‖ < 1 ∧ ‖vm‖ < 1 ∧
        (37 : ℝ) / 32 < k ∧ k < 5 / 4 ∧ 5 / 4 < mu ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1, U v ≤ mu) ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1, U v = mu ↔ v = vm) ∧
        0 < rho ∧ k < mu - 9 * rho ^ 2 ∧
        e0 0 = vm ∧ Metric.closedBall 0 (4 * rho) ⊆ e0.source ∧
        e0.target ⊆ Metric.ball 0 1 ∧
        ContDiffOn ℝ ∞ e0 e0.source ∧
        ContDiffOn ℝ ∞ e0.symm e0.target ∧
        (∀ p ∈ e0.source, U (e0 p) = mu - ‖p‖ ^ 2) ∧
        (∀ v ∈ Metric.closedBall (0 : E2) 1,
          mu - 9 * rho ^ 2 ≤ U v →
            v ∈ e0.target ∧ ‖e0.symm v‖ ≤ 3 * rho) ∧
        (∀ p ∈ Metric.closedBall (0 : E2) (3 * rho),
          L (e0 p) < mu - 9 * rho ^ 2) ∧
        e = e0.restrOpen (Metric.ball 0 (3 * rho)) isOpen_ball ∧
        e.source = Metric.ball 0 (3 * rho) ∧
        e.target = e0 '' Metric.ball 0 (3 * rho) ∧
        (∀ p : E2, e p = e0 p) ∧
        (∀ v : E2, e.symm v = e0.symm v) ∧
        ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        (∀ p ∈ e.source, U (e p) = mu - ‖p‖ ^ 2) ∧
        let nu : ℝ := mu - rho ^ 2
        let delta : ℝ := rho ^ 2 / 8
        ContDiff ℝ ∞ c ∧
        (∀ z : ℝ, c z ∈ Icc (nu - 3 * delta / 4) (nu + 3 * delta / 4)) ∧
        EqOn c id (Icc (nu - delta / 2) (nu + delta / 2)) ∧
        (∀ d : ℝ,
          let S : Set E3 := (nestedReferenceBallChart d).boundary
          (∀ y ∈ S, mu - 9 * rho ^ 2 + d ≤ H0 y →
            let v : E2 := (heightCoordinates y).1
            v ∈ e0.target ∧ ‖e0.symm v‖ ≤ 3 * rho ∧
            y = heightCoordinates.symm (v, U v + d)) ∧
          ∀ h ∈ Set.Icc (nu - delta / 4) (nu + delta / 4),
            0 < mu - h ∧ mu - h < 2 * rho ^ 2 ∧
            Metric.closedBall (0 : E2) (Real.sqrt (mu - h)) ⊆ e.source ∧
            S ∩ {y : E3 | h + d ≤ H0 y} ⊆
              {y : E3 | (heightCoordinates y).1 ∈ e.target} ∧
            S ∩ {y : E3 | h + d ≤ H0 y} =
              (fun p : E2 => heightCoordinates.symm (e p, U (e p) + d)) ''
                Metric.closedBall (0 : E2) (Real.sqrt (mu - h))) ∧
        ∀ d : ℝ,
          let r : ℝ → ℝ := fun z => Real.sqrt (mu - c (z - d))
          ∃ T : OpenPartialHomeomorph (E2 × ℝ) E3,
            ContDiff ℝ ∞ r ∧
            (∀ z : ℝ, 0 < r z ∧ (r z) ^ 2 < 2 * rho ^ 2 ∧ r z < 3 * rho) ∧
            (∀ p : E2 × ℝ, T p = C.symm (e (r p.2 • p.1), p.2)) ∧
            (∀ y : E3, T.symm y =
              ((r (C y).2)⁻¹ • e.symm (C y).1, (C y).2)) ∧
            T.source = {p : E2 × ℝ | r p.2 • p.1 ∈ e.source} ∧
            T.target = {y : E3 | (C y).1 ∈ e.target} ∧
            ContDiffOn ℝ ∞ T T.source ∧
            ContDiffOn ℝ ∞ T.symm T.target ∧
            Metric.closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
            (∀ p : E2 × ℝ, (C (T p)).2 = p.2) ∧
            (∀ y : E3, (T.symm y).2 = (C y).2) ∧
            (∀ z : ℝ, z - d ∈ Icc (nu - delta / 2) (nu + delta / 2) →
              T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ z - d ≤ U v} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ z - d < U v} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                C.symm '' ({v : E2 | v ∈ e.target ∧ U v = z - d} ×ˢ
                  ({z} : Set ℝ)) ∧
              T '' (Metric.sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
                (nestedReferenceBallChart d).boundary ∩ {y : E3 | H0 y = z}) ∧
            let S : Set E3 := (nestedReferenceBallChart d).boundary
            ∀ (P : SurgeryCapProfile) (h tau lambda : ℝ),
              h ∈ Icc (nu - delta / 4) (nu + delta / 4) →
              0 < tau → 0 < lambda →
              lambda * P.heightBound < min (delta / 16) tau →
              let beta : ℝ := delta / 16
              let s : ℝ := h + d
              let E : Set E3 := S ∩ {y : E3 | s ≤ H0 y}
              let R : Set E3 := S ∩ {y : E3 | H0 y ≤ s}
              let cap : UnitTwoSphere → E3 := fun q =>
                T ((P.model q).1, s - lambda * (P.model q).2)
              let north : Set E3 := cap '' {q : UnitTwoSphere | 0 ≤ H0 (q : E3)}
              let south : Set E3 := cap '' {q : UnitTwoSphere | H0 (q : E3) ≤ 0}
              let rim : Set E3 := T '' (Metric.sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
              let M := flatCapDiffeomorph P.horizontal P.vertical
                P.horizontal_smooth P.vertical_smooth
                (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
              ∃ (J : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
                (gA : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (a : ℝ → ℝ)
                (A : BallNeighborhoodChart E3 E3),
                (∀ q : UnitTwoSphere,
                  (H0 (q : E3) ≤ 0 →
                    J (q : E3) = (P.horizontal (H0 (q : E3)) • (C (q : E3)).1,
                      H0 (q : E3))) ∧
                  (0 ≤ H0 (q : E3) → J (q : E3) = P.model q)) ∧
                (∀ t : ℝ, gA t = -h + lambda * t - (mu - h - lambda) *
                  (1 - Real.smoothTransition (2 * t + 3 / 2))) ∧
                StrictMono gA ∧ gA (-1) = -mu ∧ gA 0 = -h ∧
                (∀ t : ℝ, -1 / 4 ≤ t → gA t = -h + lambda * t) ∧
                ContDiff ℝ ∞ a ∧ (∀ t : ℝ, 0 < a t) ∧
                (∀ t : ℝ, -1 / 8 ≤ t → a t = Real.sqrt (gA t + mu)) ∧
                (∀ t ∈ Icc (-1 : ℝ) 0,
                  a t ^ 2 * (P.horizontal t * Real.sqrt (1 - t ^ 2)) ^ 2 =
                    gA t + mu) ∧
                A.chart.source = {y : E3 | a (J y).2 • (J y).1 ∈ e.source} ∧
                A.chart.target = {y : E3 | (C y).1 ∈ e.target} ∧
                (∀ y : E3, A.chart y =
                  C.symm (e (a (J y).2 • (J y).1), d - gA (J y).2)) ∧
                (∀ y : E3, A.chart.symm y =
                  J.symm ((a (gA.symm (d - H0 y)))⁻¹ • e.symm (C y).1,
                    gA.symm (d - H0 y))) ∧
                S = E ∪ R ∧
                A.boundary = E ∪ north ∧ E ∩ north = rim ∧
                (∀ b ∈ Icc h (h + beta),
                  A.inside ∩ {y : E3 | H0 y = b + d} =
                    T '' (Metric.ball (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
                  A.closedRegion ∩ {y : E3 | H0 y = b + d} =
                    T '' (Metric.closedBall (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
                  A.boundary ∩ {y : E3 | H0 y = b + d} =
                    T '' (Metric.sphere (0 : E2) 1 ×ˢ ({b + d} : Set ℝ))) ∧
                (∀ y ∈ A.closedRegion,
                  (C y).1 ∈ e.target ∧ s - lambda * P.heightBound ≤ H0 y ∧
                  H0 y ≤ mu + d ∧ H0 y ≤ U (C y).1 + d ∧
                  L (C y).1 + d < H0 y) ∧
                (∀ y ∈ A.inside,
                  (C y).1 ∈ e.target ∧ L (C y).1 + d < H0 y ∧
                  H0 y < U (C y).1 + d) ∧
                A.closedRegion ⊆ (nestedReferenceBallChart d).closedRegion ∧
                A.inside ⊆ (nestedReferenceBallChart d).inside ∧
                (∀ q : UnitTwoSphere, -1 / 8 < H0 (q : E3) →
                  A.chart (q : E3) = cap q) ∧
                Disjoint A.inside S ∧ A.closedRegion ∩ R ⊆ north ∧
                Disjoint A.closedRegion {y : E3 | H0 y ≤ s - tau} ∧
                ∃ N : BallNeighborhoodChart E3 E3,
                  N.boundary = south ∪ north ∧
                  N.chart.source = {y : E3 |
                    ((M (C y)).1, s - lambda * (M (C y)).2) ∈ T.source} ∧
                  N.chart.target = T.target ∧
                  (∀ y : E3, N.chart y =
                    T ((M (C y)).1, s - lambda * (M (C y)).2)) ∧
                  (∀ y : E3, N.chart.symm y =
                    C.symm (M.symm ((T.symm y).1, (s - (T.symm y).2) / lambda))) ∧
                  N.closedRegion ⊆ A.closedRegion ∧
                  N.closedRegion ⊆ {y : E3 | |H0 y - s| < tau} ∧
                  north = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ H0 y} ∧
                  south ∩ north = rim ∧
                  (∀ q : UnitTwoSphere, -1 / 8 < H0 (q : E3) →
                    N.chart (q : E3) ∈ A.boundary) := by
  classical
  dsimp only
  let U : E2 → ℝ := fun v => ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let L : E2 → ℝ := fun v => ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let C := heightCoordinates
  obtain ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    rho, e0, e, c, hvs, hvm, hklo, hkhi, hmulo, hmax, hunique, hrho,
    hsep, hzero, hbuf0, htargetD, he0, he0i, hquad0, hfull, hlower0,
    hrestrict, hes, het, hefun, heinv, he, hei, heq, hc, hcr, hkid, hwhole, hTube⟩ :=
      exists_upper_reference_tube
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  let mu := U vm
  let nu := mu - rho ^ 2
  let delta := rho ^ 2 / 8
  change ∀ p ∈ e.source, U (e p) = mu - ‖p‖ ^ 2 at heq
  change ∀ p ∈ closedBall (0 : E2) (3 * rho), L (e0 p) < mu - 9 * rho ^ 2 at hlower0
  change EqOn c id (Icc (nu - delta / 2) (nu + delta / 2)) at hkid
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hdelta : 0 < delta := div_pos hrho2 (by norm_num)
  refine ⟨ws, wm, hwslo, hwsup, hwsroot, hwmp, hwmh, hwmroot,
    rho, e0, e, c, hvs, hvm, hklo, hkhi, hmulo, hmax, hunique, hrho,
    hsep, hzero, hbuf0, htargetD, he0, he0i, hquad0, hfull, hlower0,
    hrestrict, hes, het, hefun, heinv, he, hei, heq, hc, hcr, hkid, hwhole, ?_⟩
  intro d
  let r : ℝ → ℝ := fun z => Real.sqrt (mu - c (z - d))
  obtain ⟨T, hr, hrb, hTf, hTi, hTs, hTt, hT, hTinv, hTc, hTh, hTih, hcuts⟩ := hTube d
  change ∀ z, 0 < r z ∧ (r z) ^ 2 < 2 * rho ^ 2 ∧ r z < 3 * rho at hrb
  change ∀ p, T p = C.symm (e (r p.2 • p.1), p.2) at hTf
  change ∀ p, (C (T p)).2 = p.2 at hTh
  refine ⟨T, hr, hrb, hTf, hTi, hTs, hTt, hT, hTinv, hTc, hTh, hTih, hcuts, ?_⟩
  let S : Set E3 := (nestedReferenceBallChart d).boundary
  intro P h tau lambda hh htau hlambda hsmall
  let beta : ℝ := delta / 16
  let s : ℝ := h + d
  let E : Set E3 := S ∩ {y | s ≤ (C y).2}
  let R : Set E3 := S ∩ {y | (C y).2 ≤ s}
  let cap : UnitTwoSphere → E3 := fun q => T ((P.model q).1, s - lambda * (P.model q).2)
  let north : Set E3 := cap '' {q | 0 ≤ (C (q : E3)).2}
  let south : Set E3 := cap '' {q | (C (q : E3)).2 ≤ 0}
  let rim : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))
  have hM := P.one_le_heightBound
  have hsmallB : lambda * P.heightBound < beta := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hshort : lambda * P.heightBound < tau := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hlM : lambda ≤ lambda * P.heightBound := by nlinarith only [hlambda, hM]
  have hlB : lambda < beta := hlM.trans_lt hsmallB
  have hhw : nu - delta / 4 ≤ h ∧ h ≤ nu + delta / 4 := hh
  have hgap : lambda < mu - h := by
    dsimp only [nu, delta, beta] at hhw hlB
    nlinarith only [hhw.2, hlB, hrho2]
  have hupper : mu - h + lambda * P.heightBound < 2 * rho ^ 2 := by
    dsimp only [nu, delta, beta] at hhw hsmallB
    nlinarith only [hhw.1, hsmallB, hrho2]
  have hErepr : E = (fun p : E2 => C.symm (e p, U (e p) + d)) ''
      closedBall (0 : E2) (Real.sqrt (mu - h)) := ((hwhole d).2 h hh).2.2.2.2
  have hEbuf : closedBall (0 : E2) (Real.sqrt (mu - h)) ⊆ e.source :=
    ((hwhole d).2 h hh).2.2.1
  obtain ⟨J, hJhem, hJbound, hJopen, hJfiber⟩ := exists_round_profile_native_ball_model P
  change ∀ q : UnitTwoSphere,
    ((C (q : E3)).2 ≤ 0 → J q = (P.horizontal (C (q : E3)).2 • (C (q : E3)).1, (C (q : E3)).2)) ∧
    (0 ≤ (C (q : E3)).2 → J q = P.model q) at hJhem
  obtain ⟨g, a, hgf0, hgm, hgm1, hg0, hgaff, ha, hap, hatop, hasq⟩ :=
    exists_inner_reference_profile_scaling P (-h) (-mu) lambda hlambda (by linarith only [hgap])
  simp only [sub_neg_eq_add] at hatop hasq
  have hgf (t : ℝ) : g t = -h + lambda * t - (mu - h - lambda) *
      (1 - Real.smoothTransition (2 * t + 3 / 2)) := by rw [hgf0]; ring
  let rn : ℝ → ℝ := fun t => P.horizontal t * Real.sqrt (1 - t ^ 2)
  have hrn (t : ℝ) : 0 ≤ rn t := mul_nonneg (P.horizontal_pos t).le (Real.sqrt_nonneg _)
  have hapos (t : ℝ) (ht : -1 / 8 ≤ t) : 0 < g t + mu := by
    have hm' := hgm (show (-1 : ℝ) < t by linarith)
    rw [hgm1] at hm'
    linarith
  have ha2 (t : ℝ) (ht : -1 / 8 ≤ t) : a t ^ 2 = g t + mu := by
    rw [hatop t ht, Real.sq_sqrt (hapos t ht).le]
  have hns (c : ℝ) (x : E2) : ‖c • x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hdata (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      ‖a (J y).2 • (J y).1‖ ^ 2 ≤ g (J y).2 + mu ∧
      -mu ≤ g (J y).2 ∧ g (J y).2 ≤ -h + lambda * P.heightBound := by
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
    nlinarith only [hb.1, hb.2.2, hupper, hrho, hrho2,
      norm_nonneg (a (J y).2 • (J y).1)]
  let Wsource : Set (E2 × ℝ) := {p | a p.2 • p.1 ∈ e.source}
  let Wtarget : Set E3 := {y | (C y).1 ∈ e.target}
  let f : E2 × ℝ → E3 := fun p => C.symm (e (a p.2 • p.1), d - g p.2)
  let v : E3 → ℝ := fun y => g.symm (d - (C y).2)
  let fi : E3 → E2 × ℝ := fun y => ((a (v y))⁻¹ • e.symm (C y).1, v y)
  have hscale : ContDiff ℝ ∞ (fun p : E2 × ℝ => a p.2 • p.1) :=
    (ha.comp contDiff_snd).smul contDiff_fst
  have hv : ContDiff ℝ ∞ v := g.symm.contDiff.comp (contDiff_const.sub C.contDiff.snd)
  have hai : ContDiff ℝ ∞ (fun y : E3 => (a (v y))⁻¹) := (ha.comp hv).inv (fun y => (hap _).ne')
  have hf : ContDiffOn ℝ ∞ f Wsource := C.symm.contDiff.comp_contDiffOn
    ((he.comp hscale.contDiffOn (fun _ hp => hp)).prodMk
      (contDiff_const.sub (g.contDiff.comp contDiff_snd)).contDiffOn)
  have hfi : ContDiffOn ℝ ∞ fi Wtarget := (hai.contDiffOn.smul
    (hei.comp C.contDiff.fst.contDiffOn (fun _ hy => hy))).prodMk hv.contDiffOn
  have hmapf (p : E2 × ℝ) (hp : p ∈ Wsource) : f p ∈ Wtarget := by
    change (C (C.symm (e (a p.2 • p.1), d - g p.2))).1 ∈ e.target
    rw [C.apply_symm_apply]
    exact e.map_source hp
  have hmapfi (y : E3) (hy : y ∈ Wtarget) : fi y ∈ Wsource := by
    change a (v y) • ((a (v y))⁻¹ • e.symm (C y).1) ∈ e.source
    rw [smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul]
    exact e.map_target (hy)
  have hif (p : E2 × ℝ) (hp : p ∈ Wsource) : fi (f p) = p := by
    have hvf : v (f p) = p.2 := by
      dsimp only [v, f]; rw [C.apply_symm_apply, sub_sub_cancel, g.symm_apply_apply]
    dsimp only [fi]
    rw [hvf]
    dsimp only [f]
    rw [C.apply_symm_apply, e.left_inv hp, smul_smul, inv_mul_cancel₀ (hap _).ne', one_smul]
  have hff (y : E3) (hy : y ∈ Wtarget) : f (fi y) = y := by
    dsimp only [f, fi]
    rw [smul_smul, mul_inv_cancel₀ (hap _).ne', one_smul, e.right_inv (hy)]
    dsimp only [v]
    rw [g.apply_symm_apply, sub_sub_cancel, Prod.eta, C.symm_apply_apply]
  let W : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    { toFun := f, invFun := fi, source := Wsource, target := Wtarget
      map_source' := hmapf, map_target' := hmapfi, left_inv' := hif, right_inv' := hff
      open_source := e.open_source.preimage hscale.continuous
      open_target := e.open_target.preimage C.continuous.fst
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
  have hAt : A.chart.target = {y : E3 | (C y).1 ∈ e.target} := by
    ext y
    change ((C y).1 ∈ e.target ∧ fi y ∈ (univ : Set (E2 × ℝ))) ↔ _
    simp only [mem_univ, and_true, mem_ofPred_eq]
  have hAf (y : E3) : A.chart y = C.symm (e (a (J y).2 • (J y).1), d - g (J y).2) := rfl
  have hAi (y : E3) : A.chart.symm y =
      J.symm ((a (g.symm (d - (C y).2)))⁻¹ • e.symm (C y).1, g.symm (d - (C y).2)) := rfl
  have hAh (y : E3) : (C (A.chart y)).2 = d - g (J y).2 := by rw [hAf, C.apply_symm_apply]
  have hAp (y : E3) : (C (A.chart y)).1 = e (a (J y).2 • (J y).1) := by rw [hAf, C.apply_symm_apply]
  have hsolid (y : E3) (hy : y ∈ A.closedRegion) :
      (C y).1 ∈ e.target ∧ s - lambda * P.heightBound ≤ (C y).2 ∧
      (C y).2 ≤ mu + d ∧ (C y).2 ≤ U (C y).1 + d ∧ L (C y).1 + d < (C y).2 := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hb := hbuffer x hx
    have hd := hdata x hx
    have hn : ‖a (J x).2 • (J x).1‖ < 3 * rho := by rwa [hes, mem_ball_zero_iff] at hb
    have hL := hlower0 (a (J x).2 • (J x).1) (mem_closedBall_zero_iff.mpr hn.le)
    rw [← hefun] at hL
    rw [hAp, hAh]
    refine ⟨e.map_source hb, by dsimp only [s]; linarith only [hd.2.2],
      by linarith only [hd.2.1], ?_, ?_⟩
    · rw [heq _ hb]; linarith only [hd.1]
    · nlinarith only [hL, hd.2.2, hupper, hrho2]
  have hopen (y : E3) (hy : y ∈ A.inside) :
      (C y).1 ∈ e.target ∧ L (C y).1 + d < (C y).2 ∧ (C y).2 < U (C y).1 + d := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hxc := ball_subset_closedBall hx
    have hb := hbuffer x hxc
    have hd := hJbound x hxc
    have hs := hsolid (A.chart x) ⟨x, hxc, rfl⟩
    refine ⟨hs.1, hs.2.2.2.2, ?_⟩
    rw [hAp, hAh, heq _ hb, hns]
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
    have hcenter : -g (P.model q).2 ∈ Icc (nu - delta / 2) (nu + delta / 2) := by
      rw [hgaff _ (by linarith only [htlo])]
      have hlo := mul_lt_mul_of_pos_left htlo hlambda
      have hhi := mul_le_mul_of_nonneg_left hthi hlambda.le
      constructor <;> dsimp only [nu, delta, beta] at hhw hlB hsmallB ⊢ <;>
        linarith only [hhw.1, hhw.2, hlB, hsmallB, hlo, hhi]
    have har : a (P.model q).2 = r (d - g (P.model q).2) := by
      rw [hatop _ htlo.le]
      dsimp only [r]
      rw [show d - g (P.model q).2 - d = -g (P.model q).2 by ring, hkid hcenter]
      simp only [id_eq, sub_neg_eq_add, add_comm]
    rw [hAf, hj]
    change C.symm (e (a (P.model q).2 • (P.model q).1), d - g (P.model q).2) = T _
    have hz : s - lambda * (P.model q).2 = d - g (P.model q).2 := by
      rw [hgaff _ (by linarith only [htlo])]; dsimp only [s]; ring
    rw [hTf]
    change C.symm (e (a (P.model q).2 • (P.model q).1), d - g (P.model q).2) =
      C.symm (e (r (s - lambda * (P.model q).2) • (P.model q).1), s - lambda * (P.model q).2)
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
    have hu : U (e (a (J (q : E3)).2 • (J (q : E3)).1)) = -g (J (q : E3)).2 := by
      rw [heq _ hbuf, hns, hnorm, hasq _ ht]; ring
    have hgth := hgm.monotone ht.2
    rw [hg0] at hgth
    have hp2 : ‖a (J (q : E3)).2 • (J (q : E3)).1‖ ^ 2 = g (J (q : E3)).2 + mu := by
      rw [hns, hnorm, hasq _ ht]
    rw [hErepr]
    refine ⟨a (J (q : E3)).2 • (J (q : E3)).1, mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · have hs := Real.sq_sqrt (show 0 ≤ mu - h by linarith only [hgap, hlambda])
      nlinarith only [hp2, hgth, hs, Real.sqrt_nonneg (mu - h),
        norm_nonneg (a (J (q : E3)).2 • (J (q : E3)).1)]
    · change C.symm (e (a (J (q : E3)).2 • (J (q : E3)).1),
        U (e (a (J (q : E3)).2 • (J (q : E3)).1)) + d) = A.chart q
      rw [hu, hAf]; congr 2; ring
  have hback (y : E3) (hy : y ∈ E) : y ∈ A.boundary := by
    rw [hErepr] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have hps : p ∈ e.source := hEbuf hp
    have hu : U (e p) = mu - ‖p‖ ^ 2 := heq p hps
    have hph : h ≤ U (e p) := by
      have hn := mem_closedBall_zero_iff.mp hp
      have hs := Real.sq_sqrt (show 0 ≤ mu - h by linarith only [hgap, hlambda])
      nlinarith only [hn, hs, hu, norm_nonneg p, Real.sqrt_nonneg (mu - h)]
    let t := g.symm (-U (e p))
    have hgt : g t = -U (e p) := g.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hgm.le_iff_le.mp
      · rw [hgm1, hgt, hu]; nlinarith only [sq_nonneg ‖p‖]
      · rw [hgt, hg0]; linarith only [hph]
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
    rw [hAf, hj, hxp, hgt]; congr 2; ring
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
      (A.chart '' K) ∩ {y | (C y).2 = d - g t} =
        (fun x : E2 => C.symm (e (a t • x), d - g t)) '' D0 := by
    ext y; constructor
    · rintro ⟨⟨w, hw, rfl⟩, hh'⟩
      change (C (A.chart w)).2 = d - g t at hh'
      have ht : (J w).2 = t := hgm.injective (by
        rw [hAh] at hh'; linarith only [hh'])
      have hf' : J w ∈ (J '' K) ∩ {p | p.2 = t} := ⟨⟨w, hw, rfl⟩, ht⟩
      rw [hfib] at hf'
      obtain ⟨x, hx, he'⟩ := hf'
      exact ⟨x, hx, by rw [hAf, ← he']⟩
    · rintro ⟨x, hx, rfl⟩
      have hf' : (x, t) ∈ (J '' K) ∩ {p | p.2 = t} := by rw [hfib]; exact ⟨x, hx, rfl⟩
      obtain ⟨w, hw, he'⟩ := hf'.1
      exact ⟨⟨w, hw, by rw [hAf, he']⟩, by
        change (C (C.symm (e (a t • x), d - g t))).2 = _
        rw [C.apply_symm_apply]⟩
  have hCuts (b : ℝ) (hb : b ∈ Icc h (h + beta)) :
      A.inside ∩ {y | (C y).2 = b + d} = T '' (ball (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
      A.closedRegion ∩ {y | (C y).2 = b + d} = T '' (closedBall (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) ∧
      A.boundary ∩ {y | (C y).2 = b + d} = T '' (sphere (0 : E2) 1 ×ˢ ({b + d} : Set ℝ)) := by
    have hmb : b < mu := by
      dsimp only [nu, delta, beta] at hhw hb
      nlinarith only [hhw.2, hb.2, hrho2]
    have hbc : b ∈ Icc (nu - delta / 2) (nu + delta / 2) := by
      dsimp only [nu, delta, beta] at hhw hb ⊢
      constructor <;> linarith only [hhw.1, hhw.2, hb.1, hb.2]
    let t := g.symm (-b)
    have hgt : g t = -b := g.apply_symm_apply _
    have ht : t ∈ Icc (-1 : ℝ) 0 := by
      constructor <;> apply hgm.le_iff_le.mp
      · rw [hgm1, hgt]; linarith only [hmb]
      · rw [hgt, hg0]; linarith only [hb.1]
    have htm : -1 < t := hgm.lt_iff_lt.mp (by rw [hgm1, hgt]; linarith only [hmb])
    have hrnp : 0 < rn t := mul_pos (P.horizontal_pos t) (Real.sqrt_pos.mpr (by
      have hh' := mul_pos (show 0 < 1 - t by linarith only [ht.2]) (show 0 < 1 + t by linarith)
      nlinarith only [hh']))
    have hrz : r (b + d) = Real.sqrt (mu - b) := by
      dsimp only [r]; rw [add_sub_cancel_right, hkid hbc]
      rfl
    have hprod : a t * rn t = r (b + d) := by
      apply (sq_eq_sq₀ (mul_pos (hap t) hrnp).le (hrb (b + d)).1.le).mp
      rw [mul_pow, hasq t ht, hgt, hrz, Real.sq_sqrt (sub_pos.mpr hmb).le]; ring
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
    rw [hgt, show d - -b = b + d by ring, ← hbo, hscale] at ho
    rw [hgt, show d - -b = b + d by ring, ← hbc', hscale] at hc
    rw [hgt, show d - -b = b + d by ring, ← hbs, hscale] at hs
    exact ⟨ho, hc, hs⟩
  have hNorthHeight (y : E3) (hy : y ∈ north) : (C y).2 ≤ s := by
    obtain ⟨q, hq, rfl⟩ := hy
    change (C (T _)).2 ≤ s
    rw [hTh]
    have h0 : 0 ≤ (P.model q).2 := mul_nonneg (P.vertical_pos _).le hq
    nlinarith only [hlambda, h0]
  have hrimE : rim ⊆ E := by
    intro y hy
    have hz : s - d ∈ Icc (nu - delta / 2) (nu + delta / 2) := by
      dsimp only [s]; rw [add_sub_cancel_right]
      constructor <;> linarith only [hhw.1, hhw.2, hdelta]
    have he' := (hcuts s hz).2.2.2
    change rim = S ∩ {y | (C y).2 = s} at he'
    rw [he'] at hy
    exact ⟨hy.1, hy.2.ge⟩
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
    change T ((P.model q).1, s - lambda * (P.model q).2) = T (x, s)
    rw [hmodel, mul_zero, sub_zero]
  have hcutself : h ∈ Icc h (h + beta) := ⟨le_rfl, by dsimp [beta]; linarith only [hdelta]⟩
  have hmeet : E ∩ north = rim := by
    apply subset_antisymm
    · rintro y ⟨hyE, hyN⟩
      have hyh : (C y).2 = s := le_antisymm (hNorthHeight y hyN) hyE.2
      change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ))
      rw [← (hCuts h hcutself).2.2]
      exact ⟨hboundary.symm ▸ Or.inl hyE, hyh⟩
    · exact fun y hy => ⟨hrimE hy, hrimNorth hy⟩
  have htests (y : E3) (hy : (C y).1 ∈ e.target) :
      (L (C y).1 + d < (C y).2 → (C y).2 ≤ U (C y).1 + d →
        y ∈ (nestedReferenceBallChart d).closedRegion) ∧
      (L (C y).1 + d < (C y).2 → (C y).2 < U (C y).1 + d →
        y ∈ (nestedReferenceBallChart d).inside) := by
    have hy0 : (C y).1 ∈ e0.target := by rw [hrestrict] at hy; exact hy.1
    have hn := mem_ball_zero_iff.mp (htargetD hy0)
    have hnorm : ‖(C y).1‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      rfl
    have hs := Real.sq_sqrt (show 0 ≤ 1 - ‖(C y).1‖ ^ 2 by nlinarith only [hn, norm_nonneg (C y).1])
    let q : ℝ := y 2 - (y 0) ^ 2 - (y 1) ^ 2 - y 0 / 32 - d
    have hlo (hlo' : L (C y).1 + d < (C y).2) : 0 < Real.sqrt (1 - ‖(C y).1‖ ^ 2) + q := by
      change ‖(C y).1‖ ^ 2 - Real.sqrt (1 - ‖(C y).1‖ ^ 2) + y 0 / 32 + d < y 2 at hlo'
      dsimp only [q]; linarith only [hlo', hnorm]
    constructor
    · intro hl hu
      change y 2 ≤ ‖(C y).1‖ ^ 2 + Real.sqrt (1 - ‖(C y).1‖ ^ 2) + y 0 / 32 + d at hu
      have hhi : 0 ≤ Real.sqrt (1 - ‖(C y).1‖ ^ 2) - q := by
        dsimp only [q]; linarith only [hu, hnorm]
      have hp := mul_nonneg (hlo hl).le hhi
      rw [(nestedReferenceBallChart_regions d).2.2.2 y |>.2.1]
      dsimp only [q] at hp
      nlinarith only [hp, hs, hnorm]
    · intro hl hu
      change y 2 < ‖(C y).1‖ ^ 2 + Real.sqrt (1 - ‖(C y).1‖ ^ 2) + y 0 / 32 + d at hu
      have hhi : 0 < Real.sqrt (1 - ‖(C y).1‖ ^ 2) - q := by
        dsimp only [q]; linarith only [hu, hnorm]
      have hp := mul_pos (hlo hl) hhi
      rw [(nestedReferenceBallChart_regions d).2.2.2 y |>.1]
      dsimp only [q] at hp
      nlinarith only [hp, hs, hnorm]
  have hclosed : A.closedRegion ⊆ (nestedReferenceBallChart d).closedRegion := by
    intro y hy
    have hs := hsolid y hy
    exact (htests y hs.1).1 hs.2.2.2.2 hs.2.2.2.1
  have hinside : A.inside ⊆ (nestedReferenceBallChart d).inside := by
    intro y hy
    have hs := hopen y hy
    exact (htests y hs.1).2 hs.2.1 hs.2.2
  have hdis : Disjoint A.inside S :=
    Set.disjoint_left.mpr (fun _ hy hs =>
      Set.disjoint_left.mp (nestedReferenceBallChart d).inside_disjoint_boundary (hinside hy) hs)
  have hScover : S = E ∪ R := by
    ext y; constructor
    · intro hy
      rcases le_total s (C y).2 with hz | hz
      · exact Or.inl ⟨hy, hz⟩
      · exact Or.inr ⟨hy, hz⟩
    · rintro (hy | hy) <;> exact hy.1
  have havoid : A.closedRegion ∩ R ⊆ north := by
    rintro y ⟨hy, hyR⟩
    have hb : y ∈ A.boundary := by
      rw [← A.inside_union_boundary] at hy
      exact hy.resolve_left (fun hi => Set.disjoint_left.mp hdis hi hyR.1)
    rw [hboundary] at hb
    rcases hb with he' | hn
    · have hz : (C y).2 = s := le_antisymm hyR.2 he'.2
      apply hrimNorth
      change y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ))
      rw [← (hCuts h hcutself).2.2]
      exact ⟨hboundary.symm ▸ Or.inl he', hz⟩
    · exact hn
  have hlow : Disjoint A.closedRegion {y : E3 | (C y).2 ≤ s - tau} := by
    apply Set.disjoint_left.mpr
    intro y hy hz
    have hh' := (hsolid y hy).2.1
    change (C y).2 ≤ s - tau at hz
    linarith only [hh', hz, hshort]
  let D : (E2 × ℝ) ≃ₜ (E2 × ℝ) :=
    { toEquiv := { toFun := fun p => (p.1, -p.2), invFun := fun p => (p.1, -p.2)
                   left_inv := by intro p; simp
                   right_inv := by intro p; simp }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let Tm := D.transOpenPartialHomeomorph T
  have hTm : ContDiffOn ℝ ∞ Tm Tm.source :=
    hT.comp (by fun_prop : ContDiffOn ℝ ∞ (fun p : E2 × ℝ => (p.1, -p.2)) Tm.source)
      (fun _ hp => hp)
  have hTmi : ContDiffOn ℝ ∞ Tm.symm Tm.target := hTinv.fst.prodMk hTinv.snd.neg
  have hTmc : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tm.source :=
    fun _ hp => hTc ⟨hp.1, mem_univ _⟩
  have hTmslice (D0 : Set E2) (z : ℝ) :
      Tm '' (D0 ×ˢ ({z} : Set ℝ)) = T '' (D0 ×ˢ ({-z} : Set ℝ)) := by
    ext y; constructor
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      have hw' : w = z := hw
      subst w
      exact ⟨(x, -z), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      have hw' : w = -z := hw
      subst w
      exact ⟨(x, z), ⟨hx, rfl⟩, rfl⟩
  have huNorm : ‖C.symm ((0 : E2), (1 : ℝ))‖ = 1 := by
    have hs := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, zero_add] at hs
    nlinarith only [hs, norm_nonneg (C.symm ((0 : E2), (1 : ℝ)))]
  let u : UnitTwoSphere := ⟨-C.symm (0, 1),
    mem_sphere_zero_iff_norm.mpr (by simpa only [norm_neg] using huNorm)⟩
  have hu (y : E3) : inner ℝ (u : E3) y = -(C y).2 := by
    change inner ℝ (-heightCoordinates.symm ((0 : E2), (1 : ℝ))) y = -(heightCoordinates y).2
    simp only [inner_neg_left, heightCoordinates_symm_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three, heightCoordinates_snd_apply]
    simp
  have hheight (p : E2 × ℝ) (_hp : p ∈ Tm.source) : inner ℝ (u : E3) (Tm p) = p.2 := by
    rw [hu]; change -(C (T (p.1, -p.2))).2 = p.2
    rw [hTh, neg_neg]
  have hfilled (z : ℝ) (hz : z ∈ Icc (-s - beta) (-s)) :
      Tm '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ⊆ A.closedRegion := by
    have hb : -z - d ∈ Icc h (h + beta) := by
      dsimp only [s] at hz
      constructor <;> linarith only [hz.1, hz.2]
    have he' := (hCuts (-z - d) hb).2.1
    rw [sub_add_cancel] at he'
    rw [hTmslice, ← he']
    exact inter_subset_left
  have hneg (t : ℝ) : -(-s + lambda * t) = s - lambda * t := by ring
  have hmplace (x : E2) (t : ℝ) : Tm (x, -s + lambda * t) = T (x, s - lambda * t) := by
    change T (x, -(-s + lambda * t)) = _
    rw [hneg]
  have hcapm : (fun q : UnitTwoSphere => Tm ((P.model q).1, -s + lambda * (P.model q).2)) = cap :=
    funext (fun q => hmplace (P.model q).1 (P.model q).2)
  have hnorth : north ⊆ A.closedRegion := by
    intro y hy
    rw [← A.inside_union_boundary]
    exact Or.inr (hboundary.symm ▸ Or.inr hy)
  obtain ⟨N, hNb, hNs, hNt, hNf, hNi, hNc, hNh, hNnorth, hNmeet⟩ :=
    exists_saddle_contained_profile_ball P u Tm hTmc hTm hTmi hheight A (-s - beta) (-s) lambda tau
      hlambda (by linarith only [hsmallB]) hshort hfilled (by rw [hcapm]; exact hnorth)
  rw [hcapm] at hNb hNnorth hNmeet
  let M := flatCapDiffeomorph P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  change N.chart.source = {y : E3 | ((M (C y)).1, -(-s + lambda * (M (C y)).2)) ∈ T.source} at hNs
  simp only [hneg] at hNs
  change N.chart.target = T.target at hNt
  have hNf' (y : E3) : N.chart y = T ((M (C y)).1, s - lambda * (M (C y)).2) := by
    rw [hNf]; exact hmplace _ _
  have hNi' (y : E3) : N.chart.symm y =
      C.symm (M.symm ((T.symm y).1, (s - (T.symm y).2) / lambda)) := by
    rw [hNi]
    change C.symm (M.symm ((T.symm y).1, (-(T.symm y).2 - -s) / lambda)) = _
    rw [show -(T.symm y).2 - -s = s - (T.symm y).2 by ring]
  have hNheight : N.closedRegion ⊆ {y : E3 | |(C y).2 - s| < tau} := by
    intro y hy
    have hh' := hNh hy
    change |inner ℝ (u : E3) y - -s| < tau at hh'
    rw [hu, show -(C y).2 - -s = -((C y).2 - s) by ring, abs_neg] at hh'
    exact hh'
  rw [hTmslice, neg_neg] at hNmeet
  refine ⟨J, g, a, A, hJhem, hgf, hgm, hgm1, hg0, hgaff, ha, hap, hatop, hasq,
    hAs, hAt, hAf, hAi, hScover, hboundary, hmeet, hCuts, hsolid, hopen, hclosed, hinside,
    hpatch, hdis, havoid, hlow, N, hNb, hNs, hNt, hNf', hNi', hNc, hNheight, hNnorth, hNmeet, ?_⟩
  intro q hq
  rw [hNf']
  change cap q ∈ A.boundary
  rw [← hpatch q hq]
  exact ⟨q, q.property, rfl⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
