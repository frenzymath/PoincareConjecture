import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_outer_reference_graph_flow
    (F : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (g D : E2 → ℝ)
    (hD : ContDiff ℝ ∞ D) (hcD : HasCompactSupport D)
    (hsD : tsupport D ⊆ F '' ball (0 : E2) 1)
    (hB : F '' closedBall (0 : E2) 1 ⊆
      ball (0 : E2) (Real.sqrt 4095 / 64))
    (h lambda d : ℝ) (hh : |h - 17 / 16| ≤ 1 / 32768)
    (hlambda : 0 < lambda) (hsmall : lambda < 1 / 131072)
    (hgraph : ∀ v ∈ F '' closedBall (0 : E2) 1,
      D v = g v - (‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32))
    (hg : ∀ v ∈ F '' closedBall (0 : E2) 1,
      h ≤ g v ∧ g v ≤ h + lambda) :
    let B : Set E2 := F '' closedBall (0 : E2) 1
    let A : Set E2 := F '' ball (0 : E2) 1
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let L : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let gap : ℝ := min (1 / 32) (h - 33 / 32)
    let Omega : Set (E2 × ℝ) :=
      {y | y.1 ∈ A ∧ L y.1 + d + gap / 2 < y.2 ∧ y.2 < d + 2}
    ∃ (V : ℝ × (E2 × ℝ) → E2 × ℝ) (K M : ℝ≥0)
      (hK : LipschitzWith K (clockField V))
      (hM : ∀ p, ‖clockField V p‖ ≤ M)
      (hV : ContDiff ℝ ∞ V) (hsV : HasCompactSupport V),
      let Phi : ℝ → Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
          (E2 × ℝ) (E2 × ℝ) ∞ :=
        fun t => clockEvolutionDiffeomorph V hK hM hV hsV 0 t
      ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => Phi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (Phi p.1).symm p.2) ∧
      (∀ y : E2 × ℝ, Phi 0 y = y) ∧
      (∀ (t : ℝ) (y : E2 × ℝ),
        (Phi t).symm y = clockEvolution V hK hM t 0 y) ∧
      (∃ S : Set (E2 × ℝ), IsCompact S ∧ S ⊆ Omega ∧
        ∀ t : ℝ,
          tsupport (fun y : E2 × ℝ => Phi t y - y) ⊆ S ∧
          tsupport (fun y : E2 × ℝ => (Phi t).symm y - y) ⊆ S) ∧
      (∀ (t : ℝ) (y : E2 × ℝ), y ∉ Omega →
        Phi t y = y ∧ (Phi t).symm y = y) ∧
      (∀ (t : ℝ) (y : E2 × ℝ),
        (Phi t y).1 = y.1 ∧ ((Phi t).symm y).1 = y.1) ∧
      (∀ (t : ℝ) (v : E2),
        Phi t (v, L v + d) = (v, L v + d) ∧
        (Phi t).symm (v, L v + d) = (v, L v + d)) ∧
      (∀ (t : ℝ) (v : E2),
        Phi t (v, U v + d) =
          (v, U v + d + Real.smoothTransition t * D v)) ∧
      (∀ (t : ℝ) (v : E2),
        StrictMono (fun z : ℝ => (Phi t (v, z)).2) ∧
        StrictMono (fun z : ℝ => ((Phi t).symm (v, z)).2)) ∧
      ∀ v ∈ B,
        Phi 1 '' ({v} ×ˢ Icc (L v + d) (U v + d)) =
          {v} ×ˢ Icc (L v + d) (g v + d) ∧
        Phi 1 '' ({v} ×ˢ Ioo (L v + d) (U v + d)) =
          {v} ×ˢ Ioo (L v + d) (g v + d) := by
  let B : Set E2 := F '' closedBall (0 : E2) 1
  let A : Set E2 := F '' ball (0 : E2) 1
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let L : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 - Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let gap : ℝ := min (1 / 32) (h - 33 / 32)
  let Omega : Set (E2 × ℝ) :=
    {y | y.1 ∈ A ∧ L y.1 + d + gap / 2 < y.2 ∧ y.2 < d + 2}
  have hAB : A ⊆ B := image_mono ball_subset_closedBall
  have hA : IsOpen A := F.toHomeomorph.isOpenMap _ isOpen_ball
  have hcoord : Continuous (fun v : E2 => v 0 / (32 : ℝ)) :=
    (EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).continuous.div_const 32
  have hU : Continuous U :=
    ((continuous_norm.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add hcoord
  have hL : Continuous L :=
    ((continuous_norm.pow 2).sub
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add hcoord
  have hOmega : IsOpen Omega :=
    (hA.preimage continuous_fst).inter
      ((isOpen_lt (((hL.comp continuous_fst).add continuous_const).add continuous_const)
        continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hhlo := (abs_le.mp hh).1
  have hhhi := (abs_le.mp hh).2
  have hgap : 0 < gap := lt_min (by norm_num) (by linarith only [hhlo])
  have hgap1 : gap ≤ 1 / 32 := min_le_left _ _
  have hgap2 : gap ≤ h - 33 / 32 := min_le_right _ _
  have hg2 : h + lambda < 2 := by linarith only [hhhi, hlambda, hsmall]
  have hbounds (v : E2) (hv : v ∈ B) :
      L v + gap ≤ U v ∧ L v + gap ≤ g v ∧ U v < 2 ∧ g v < 2 := by
    have hr : ‖v‖ < Real.sqrt 4095 / 64 := by
      simpa only [mem_ball, dist_zero_right] using hB hv
    have hrsq : ‖v‖ ^ 2 < 4095 / 4096 := by
      have hp := (sq_lt_sq₀ (norm_nonneg v) (by positivity : 0 ≤ Real.sqrt 4095 / 64)).mpr hr
      norm_num [div_pow, Real.sq_sqrt] at hp
      exact hp
    have hn : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hv0 : v 0 ≤ 1 := by nlinarith only [hn, hrsq, sq_nonneg (v 1)]
    have ha0 : 0 ≤ Real.sqrt (1 - ‖v‖ ^ 2) := Real.sqrt_nonneg _
    have ha2 : (Real.sqrt (1 - ‖v‖ ^ 2)) ^ 2 = 1 - ‖v‖ ^ 2 :=
      Real.sq_sqrt (by linarith only [hrsq])
    have ha : 1 / 64 < Real.sqrt (1 - ‖v‖ ^ 2) := by
      nlinarith only [ha0, ha2, hrsq]
    have hlo : L v ≤ 33 / 32 := by
      dsimp only [L]
      linarith only [hrsq, ha0, hv0]
    have hup : U v ≤ 41 / 32 := by
      dsimp only [U]
      nlinarith only [ha2, hv0, sq_nonneg (Real.sqrt (1 - ‖v‖ ^ 2) - 1 / 2)]
    refine ⟨?_, ?_, by linarith only [hup], (hg v hv).2.trans_lt hg2⟩
    · dsimp only [L, U]
      linarith only [ha, hgap1]
    · linarith only [hlo, hgap2, (hg v hv).1]
  let T : Set (E2 × ℝ) :=
    (fun p : E2 × ℝ => (p.1, U p.1 + d + p.2 * D p.1)) ''
      (tsupport D ×ˢ Icc (0 : ℝ) 1)
  have hT : IsCompact T :=
    (hcD.isCompact.prod isCompact_Icc).image
      (continuous_fst.prodMk (((hU.comp continuous_fst).add continuous_const).add
        (continuous_snd.mul (hD.continuous.comp continuous_fst))))
  have hTO : T ⊆ Omega := by
    rintro _ ⟨⟨v, s⟩, ⟨hv, hs⟩, rfl⟩
    have hvA := hsD hv
    have hvB := hAB hvA
    obtain ⟨hloU, hlog, hhiU, hhig⟩ := hbounds v hvB
    have heq : U v + s * D v = (1 - s) * U v + s * g v := by
      rw [hgraph v hvB]
      dsimp only [U]
      ring
    have hlo : L v + gap ≤ U v + s * D v := by
      rw [heq]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hloU),
        mul_nonneg hs.1 (sub_nonneg.mpr hlog)]
    have hhi : U v + s * D v < 2 := by
      rw [heq]
      rcases eq_or_lt_of_le hs.2 with hs1 | hs1
      · dsimp only at hs1
        subst s
        simpa only [sub_self, zero_mul, one_mul, zero_add] using hhig
      · calc
          (1 - s) * U v + s * g v < (1 - s) * 2 + s * 2 :=
            add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left hhiU (sub_pos.mpr hs1))
              (mul_le_mul_of_nonneg_left hhig.le hs.1)
          _ = 2 := by ring
    exact ⟨hvA, by dsimp only; linarith only [hlo, hgap],
      by dsimp only; linarith only [hhi]⟩
  obtain ⟨xi, hxi, hcxi, hsxi, hnxi, _⟩ := exists_compact_smooth_cutoff hT hOmega hTO
  have hxiOne (y : E2 × ℝ) (hy : y ∈ T) : xi y = 1 :=
    subset_of_mem_nhdsSet hnxi hy
  let V : ℝ × (E2 × ℝ) → E2 × ℝ :=
    fun p => (0, deriv Real.smoothTransition p.1 * D p.2.1 * xi p.2)
  have hdpsi : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    Real.smoothTransition.contDiff.deriv'
  have hV : ContDiff ℝ ∞ V :=
    contDiff_const.prodMk (((hdpsi.comp contDiff_fst).mul
      (hD.comp contDiff_snd.fst)).mul (hxi.comp contDiff_snd))
  have htime (t : ℝ) (ht : t ∉ Icc (0 : ℝ) 1) : deriv Real.smoothTransition t = 0 := by
    by_cases ht0 : t < 0
    · have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds ht0] with a ha
        exact Real.smoothTransition.zero_of_nonpos ha.le
      rw [heq.deriv_eq, deriv_const]
    · have ht1 : 1 < t := lt_of_not_ge (fun hle => ht ⟨le_of_not_gt ht0, hle⟩)
      have heq : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht1] with a ha
        exact Real.smoothTransition.one_of_one_le ha.le
      rw [heq.deriv_eq, deriv_const]
  have hsV : HasCompactSupport V := by
    apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hcxi.isCompact).of_isClosed_subset
      (isClosed_tsupport V)
    apply closure_minimal ?_ (isClosed_Icc.prod (isClosed_tsupport xi))
    intro p hp
    constructor
    · by_contra ht
      exact hp (by simp only [V, htime p.1 ht, zero_mul, Prod.zero_eq_mk])
    · by_contra hy
      exact hp (by simp only [V, image_eq_zero_of_notMem_tsupport hy, mul_zero,
        Prod.zero_eq_mk])
  obtain ⟨K, M, hK, hM⟩ := clockField_bounds V hV hsV
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞ :=
    fun t => clockEvolutionDiffeomorph V hK hM hV hsV 0 t
  have hPhi : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => Phi p.1 p.2) :=
    (clockEvolution_contDiff V hK hM hV hsV).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hPhii : ContDiff ℝ ∞ (fun p : ℝ × (E2 × ℝ) => (Phi p.1).symm p.2) :=
    (clockEvolution_contDiff V hK hM hV hsV).comp
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hfix (s t : ℝ) (y : E2 × ℝ) (hy : y ∉ tsupport xi) :
      clockEvolution V hK hM s t y = y := by
    apply clockEvolution_eq_self V hK hM y
    intro a
    simp only [V, image_eq_zero_of_notMem_tsupport hy, mul_zero, Prod.zero_eq_mk]
  have hfixO (t : ℝ) (y : E2 × ℝ) (hy : y ∉ Omega) :
      Phi t y = y ∧ (Phi t).symm y = y :=
    ⟨hfix 0 t y (fun hyS => hy (hsxi hyS)), hfix t 0 y (fun hyS => hy (hsxi hyS))⟩
  have hhoriz (s t : ℝ) (y : E2 × ℝ) :
      (clockEvolution V hK hM s t y).1 = y.1 := by
    let P : (ℝ × (E2 × ℝ)) →L[ℝ] E2 :=
      (ContinuousLinearMap.fst ℝ E2 ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (E2 × ℝ))
    exact boundedFlow_preserves_linear (clockField V) hK hM P (fun _ => rfl) (s, y) (t - s)
  have hlow (t : ℝ) (v : E2) :
      Phi t (v, L v + d) = (v, L v + d) ∧
      (Phi t).symm (v, L v + d) = (v, L v + d) := by
    apply hfixO
    intro hy
    have hb := hy.2.1
    dsimp only at hb
    linarith only [hb, hgap]
  have htrack (t : ℝ) (v : E2) : Phi t (v, U v + d) =
      (v, U v + d + Real.smoothTransition t * D v) := by
    let gamma : ℝ → E2 × ℝ :=
      fun a => (v, U v + d + Real.smoothTransition a * D v)
    have hd (a : ℝ) : HasDerivAt gamma (V (a, gamma a)) a := by
      have hpsi : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition a) a :=
        ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
          (by simp)).differentiableAt.hasDerivAt
      have hderiv : HasDerivAt gamma (0, deriv Real.smoothTransition a * D v) a := by
        simpa only [gamma, Pi.add_apply, zero_add] using (hasDerivAt_const a v).prodMk
          ((hasDerivAt_const a (U v + d)).add
            (hpsi.mul_const (D v)))
      by_cases hv : v ∈ tsupport D
      · have hxiG : xi (gamma a) = 1 := hxiOne _
          ⟨(v, Real.smoothTransition a),
            ⟨hv, Real.smoothTransition.nonneg a, Real.smoothTransition.le_one a⟩, rfl⟩
        simpa only [V, hxiG, mul_one] using hderiv
      · have hz := image_eq_zero_of_notMem_tsupport hv
        simpa only [V, gamma, hz, mul_zero, zero_mul] using hderiv
    have hzero : gamma 0 = (v, U v + d) := by
      simp only [gamma, Real.smoothTransition.zero, zero_mul, add_zero]
    have hz : (0 : ℝ) ∈ Ioo (min 0 t - 1) (max 0 t + 1) :=
      ⟨by linarith [min_le_left (0 : ℝ) t], by linarith [le_max_left (0 : ℝ) t]⟩
    have ht : t ∈ Ioo (min 0 t - 1) (max 0 t + 1) :=
      ⟨by linarith [min_le_right (0 : ℝ) t], by linarith [le_max_right (0 : ℝ) t]⟩
    change clockEvolution V hK hM 0 t (v, U v + d) = gamma t
    simpa only [hzero] using clockEvolution_tracks V hK hM gamma hz (fun a _ => hd a) ht
  have horder (G : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞)
      (hG : ∀ y : E2 × ℝ, (G y).1 = y.1)
      (hGfix : ∀ y : E2 × ℝ, y ∉ Omega → G y = y) (v : E2) :
      StrictMono (fun z : ℝ => (G (v, z)).2) := by
    have hc : Continuous (fun z : ℝ => (G (v, z)).2) :=
      (G.contMDiff.continuous.comp (continuous_const.prodMk continuous_id)).snd
    have hinj : Function.Injective (fun z : ℝ => (G (v, z)).2) := by
      intro a b hab
      have he : G (v, a) = G (v, b) :=
        Prod.ext ((hG (v, a)).trans (hG (v, b)).symm) hab
      exact congrArg Prod.snd (G.injective he)
    rcases hc.strictMono_of_inj hinj with hm | ha
    · exact hm
    · have hfix2 : G (v, d + 2) = (v, d + 2) := hGfix _ (fun hy => lt_irrefl _ hy.2.2)
      have hfix3 : G (v, d + 3) = (v, d + 3) := hGfix _ (fun hy => by
        have hb := hy.2.2
        dsimp only at hb
        linarith only [hb])
      have hbad := ha (show d + 2 < d + 3 by linarith)
      dsimp only at hbad
      rw [hfix2, hfix3] at hbad
      dsimp only at hbad
      linarith only [hbad]
  have hmono (t : ℝ) (v : E2) :
      StrictMono (fun z : ℝ => (Phi t (v, z)).2) ∧
      StrictMono (fun z : ℝ => ((Phi t).symm (v, z)).2) :=
    ⟨horder (Phi t) (hhoriz 0 t) (fun y hy => (hfixO t y hy).1) v,
      horder (Phi t).symm (hhoriz t 0) (fun y hy => (hfixO t y hy).2) v⟩
  refine ⟨V, K, M, hK, hM, hV, hsV, hPhi, hPhii,
    fun y => clockEvolution_self V hK hM 0 y, fun _ _ => rfl, ?_, hfixO,
    fun t y => ⟨hhoriz 0 t y, hhoriz t 0 y⟩, hlow, htrack, hmono, ?_⟩
  · refine ⟨tsupport xi, hcxi.isCompact, hsxi, ?_⟩
    intro t
    constructor
    · apply closure_minimal ?_ (isClosed_tsupport xi)
      intro y hy
      by_contra hny
      exact hy (sub_eq_zero.mpr (hfix 0 t y hny))
    · apply closure_minimal ?_ (isClosed_tsupport xi)
      intro y hy
      by_contra hny
      exact hy (sub_eq_zero.mpr (hfix t 0 y hny))
  · intro v hv
    have himage (J : Set ℝ) : Phi 1 '' ({v} ×ˢ J) =
        {v} ×ˢ ((fun z : ℝ => (Phi 1 (v, z)).2) '' J) := by
      ext y
      constructor
      · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
        have hwv : w = v := mem_singleton_iff.mp hw
        subst w
        exact ⟨hhoriz 0 1 (v, z), z, hz, rfl⟩
      · rintro ⟨hy, z, hz, hzy⟩
        refine ⟨(v, z), ⟨rfl, hz⟩, Prod.ext ?_ hzy⟩
        exact (hhoriz 0 1 (v, z)).trans (mem_singleton_iff.mp hy).symm
    have hc : Continuous (fun z : ℝ => (Phi 1 (v, z)).2) :=
      ((Phi 1).contMDiff.continuous.comp (continuous_const.prodMk continuous_id)).snd
    have hlo : (Phi 1 (v, L v + d)).2 = L v + d := congrArg Prod.snd (hlow 1 v).1
    have hhi : (Phi 1 (v, U v + d)).2 = g v + d := by
      rw [htrack, Real.smoothTransition.one, one_mul]
      dsimp only
      rw [hgraph v hv]
      dsimp only [U]
      ring
    constructor
    · rw [himage, hc.image_Icc_of_strictMono (hmono 1 v).1, hlo, hhi]
    · rw [himage, hc.image_Ioo_of_strictMono (hmono 1 v).1, hlo, hhi]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
