import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceSelectedWallField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology Matrix NNReal

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_reference_selected_wall_transport
    (ws wm d sigma : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (m : OpenPartialHomeomorph E2 (ℝ × ℝ))
    (hm_point : (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) ∈ m.source)
    (hm_source : m.source ⊆ Metric.ball (0 : E2) 1)
    (hm_zero : m (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) = 0)
    (hm : ContDiffOn ℝ ∞ m m.source)
    (hmi : ContDiffOn ℝ ∞ m.symm m.target)
    (hm_height : ∀ v ∈ m.source,
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
        1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 -
          (m v).1 ^ 2 + (m v).2 ^ 2) :
    let h8 := exists_nestedReference_buffered_morse_chart
      ws hwslo hwshi m hm_point hm_source hm_zero hm hmi hm_height
    let R : ℝ := Classical.choose h8
    let h8R := Classical.choose_spec h8
    let _b : ℝ := Classical.choose h8R
    let h8b := Classical.choose_spec h8R
    let e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ) :=
      Classical.choose h8b
    let rhoN : ℝ := R / 2
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    ∀ (delta : ℝ) (hdelta : 0 < delta) (hdeltaR : delta ≤ rhoN ^ 2 / 128)
      (hgapLo : 4 * delta < k - 17 / 16) (hgapHi : 4 * delta < mu - k),
    let hField := exists_reference_selected_wall_field ws wm d sigma
      hwslo hwshi hwsroot hwmlo hwmhi hwmroot hsigma
      m hm_point hm_source hm_zero hm hmi hm_height
      delta hdelta hdeltaR hgapLo hgapHi
    let hFieldF := Classical.choose_spec hField
    let X : E3 → E3 := Classical.choose hFieldF
    let hFieldX := Classical.choose_spec hFieldF
    let hX : ContDiff ℝ ∞ X := hFieldX.2.2.1
    let hcX : HasCompactSupport X := hFieldX.2.2.2.1
    let psi : UnitTwoSphere × ℝ → E3 := fun p =>
      nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
    let S : Set E3 := (nestedReferenceBallChart d).boundary
    let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
    let Do : ℝ → Set UnitTwoSphere := fun r =>
      e.symm '' {s | r2 s < r ^ 2}
    let Dc : ℝ → Set UnitTwoSphere := fun r =>
      e.symm '' {s | r2 s ≤ r ^ 2}
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
      (sx i * Real.sqrt ((rhoN ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
        sy i * Real.sqrt ((rhoN ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
    let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere := fun i p =>
      e.symm (sigma * (xi i p).2, sigma * (xi i p).1)
    let Elevel : ℝ → Set E3 := fun t =>
      (S ∩ {y : E3 | H0 y = k + d + t}) \ (j '' Do rhoN)
    ∃ (K B : ℝ≥0) (hK : LipschitzWith K X) (hB : ∀ y : E3, ‖X y‖ ≤ B),
    let T : ℝ → ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
      fun s t => boundedFlowDiffeomorph X hK hB hX hcX (t - s)
    let C : Set E3 := tsupport X
    IsCompact S ∧ IsCompact C ∧
      C ⊆ (U ∩ {y : E3 | |H0 y - (k + d)| < 4 * delta}) \
        (j '' Dc (rhoN / 4)) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => T p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 => (T p.1.1 p.1.2).symm p.2) ∧
      (∀ s t : ℝ, ∀ y : E3,
        T s t y = boundedFlow X hK hB y (t - s) ∧
        (T s t).symm y = boundedFlow X hK hB y (s - t)) ∧
      (∀ s : ℝ, ∀ y : E3, T s s y = y) ∧
      (∀ s t : ℝ, ∀ y : E3,
        HasDerivAt (fun a : ℝ => T s a y) (X (T s t y)) t) ∧
      (∀ s t : ℝ,
        tsupport (fun y : E3 => T s t y - y) ⊆ C ∧
        tsupport (fun y : E3 => (T s t).symm y - y) ⊆ C) ∧
      (∀ s t : ℝ, T s t '' S = S ∧ (T s t).symm '' S = S) ∧
      (∀ s t : ℝ, ∀ y : E3,
        (y ∈ j '' Dc (rhoN / 4) ∨ 4 * delta ≤ |H0 y - (k + d)|) →
          T s t y = y ∧ (T s t).symm y = y) ∧
      (∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ t : ℝ, |t| ≤ 2 * delta →
          HasDerivAt (fun v : ℝ => j (q i (v, a)))
            (X (j (q i (t, a)))) t) ∧
      (∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          T s t (j (q i (s, a))) = j (q i (t, a)) ∧
          (T s t).symm (j (q i (t, a))) = j (q i (s, a))) ∧
      ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
        T s t '' Elevel s = Elevel t ∧
        (T s t).symm '' Elevel t = Elevel s := by
  classical

  have hb : ∀ Y : E3 → E3, ContDiff ℝ ∞ Y → HasCompactSupport Y →
      ∃ K B : ℝ≥0, LipschitzWith K Y ∧ ∀ y : E3, ‖Y y‖ ≤ B :=
    fun Y hY hcY => compactField_bounds Y hY hcY
  intro h8 R h8R _b h8b e rhoN k mu
  have hR : 0 < R := Exists.elim (Classical.choose_spec h8b) (fun _ h => h.1)
  have hrho : 0 < rhoN := half_pos hR
  intro delta hdelta hdeltaR hgapLo hgapHi
    hField hFieldF X hFieldX hX hcX psi j H0 U S r2 Do Dc sx sy xi q Elevel
  let f : E3 → ℝ := Classical.choose hField
  have hf : ContDiffOn ℝ ∞ f U := hFieldX.1
  have hfpsi : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
      f (psi p) = p.2 := hFieldX.2.1
  have hXs : tsupport X ⊆ (U ∩ {y : E3 | |H0 y - (k + d)| < 4 * delta}) \
      (j '' Dc (rhoN / 4)) := hFieldX.2.2.2.2.1
  have hXf : ∀ y : E3, fderiv ℝ f y (X y) = 0 := hFieldX.2.2.2.2.2.1
  have hXH : ∀ p : UnitTwoSphere, |H0 (j p) - (k + d)| ≤ 3 * delta →
      p ∉ Do (rhoN / 2) → H0 (X (j p)) = 1 := hFieldX.2.2.2.2.2.2.1
  have hRadial : ∀ r : ℝ, 0 < r → r ≤ 5 * rhoN / 4 →
      IsOpen (Do r) ∧ IsCompact (Dc r) ∧ closure (Do r) = Dc r :=
    hFieldX.2.2.2.2.2.2.2.1
  have hwall : ∀ t : ℝ, |t| ≤ 2 * delta →
    {p : UnitTwoSphere | p ∈ Dc rhoN \ Do rhoN ∧ H0 (j p) = k + d + t} =
      range (fun i : Fin 4 => q i (t, 0)) := hFieldX.2.2.2.2.2.2.2.2.2.1
  have hder : ∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
      ∀ t : ℝ, |t| ≤ 2 * delta →
        HasDerivAt (fun v : ℝ => j (q i (v, a))) (X (j (q i (t, a)))) t :=
    hFieldX.2.2.2.2.2.2.2.2.2.2
  have hBounds : ∃ K B : ℝ≥0, LipschitzWith K X ∧ ∀ y : E3, ‖X y‖ ≤ B := hb X hX hcX
  let K : ℝ≥0 := Classical.choose hBounds
  let B : ℝ≥0 := Classical.choose (Classical.choose_spec hBounds)
  have hKB : LipschitzWith K X ∧ ∀ y : E3, ‖X y‖ ≤ B :=
    Classical.choose_spec (Classical.choose_spec hBounds)
  have hK : LipschitzWith K X := hKB.1
  have hB : ∀ y : E3, ‖X y‖ ≤ B := hKB.2
  let H : E3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ E2 ℝ).comp heightCoordinates.toContinuousLinearMap
  let c : ℝ := k + d
  have hpsi : IsCollarEmbedding psi := (exists_nestedReference_collar d).1
  have hRange : range j = S := (exists_nestedReference_collar d).2.1
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hji : Injective j := by
    intro p z hpz
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpz)
  have hjS (p : UnitTwoSphere) : j p ∈ S := hRange ▸ mem_range_self p
  have hS : IsCompact S := hRange ▸ isCompact_range hj
  have hU : IsOpen U := collar_image_open psi hpsi
  have hjU (p : UnitTwoSphere) : j p ∈ U :=
    ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hzero (y : E3) (hy : y ∉ U) : X y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hy (hXs hh).1.1)
  have hflow : ∀ y ∈ S, ∀ t : ℝ, boundedFlow X hK hB y t ∈ S := by
    intro y hy t
    obtain ⟨p, rfl⟩ : y ∈ range j := hRange.symm ▸ hy
    have hstay := boundedFlow_mapsTo_set X hK hB hzero t (hjU p)
    have hint := boundedFlow_preserves_firstIntegral X hK hB hzero f
      (fun z hz => (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      (fun z _ => hXf z) (j p) (hjU p) t
    have hfv : f (boundedFlow X hK hB (j p) t) = 0 :=
      hint.trans (hfpsi (p, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨z, r⟩, hzr, heq⟩ := hstay
    have hr : r = 0 := (hfpsi (z, r) hzr).symm.trans ((congrArg f heq).trans hfv)
    subst r
    exact (congrArg (fun y : E3 => y ∈ S) heq).mp (hjS z)
  have hSimage (t : ℝ) : (fun y => boundedFlow X hK hB y t) '' S = S := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact hflow z hz t
    · intro y hy
      exact ⟨boundedFlow X hK hB y (-t), hflow y hy (-t),
        by simpa only [neg_neg] using boundedFlow_neg X hK hB y (-t)⟩
  have hflowc (y : E3) : Continuous (boundedFlow X hK hB y) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (boundedFlow_hasDerivAt X hK hB y t).continuousAt)
  have hq0 (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (t : ℝ)
      (ht : |t| ≤ 2 * delta) :
      boundedFlow X hK hB (j (q i (0, a))) t = j (q i (t, a)) := by
    have hc : ContinuousOn (fun v : ℝ => j (q i (v, a)))
        (Icc (-(2 * delta)) (2 * delta)) :=
      fun v hv => (hder i a ha v (abs_le.mpr hv)).continuousAt.continuousWithinAt
    have hu := ODE_solution_unique_of_mem_Icc (v := fun _ : ℝ => X) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-(2 * delta)) (2 * delta) from
        ⟨by linarith only [hdelta], by linarith only [hdelta]⟩)
      (hflowc (j (q i (0, a)))).continuousOn
      (fun v _ => boundedFlow_hasDerivAt X hK hB (j (q i (0, a))) v)
      (fun _ _ => mem_univ _) hc
      (fun v hv => hder i a ha v (abs_le.mpr ⟨hv.1.le, hv.2.le⟩))
      (fun _ _ => mem_univ _) (boundedFlow_zero X hK hB (j (q i (0, a))))
    exact hu (abs_le.mp ht)
  have hqflow (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (s t : ℝ)
      (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta) :
      boundedFlow X hK hB (j (q i (s, a))) (t - s) = j (q i (t, a)) := by
    calc
      _ = boundedFlow X hK hB (boundedFlow X hK hB (j (q i (0, a))) s) (t - s) := by
        rw [hq0 i a ha s hs]
      _ = boundedFlow X hK hB (j (q i (0, a))) t := by
        rw [← boundedFlow_add]
        congr 1
        ring
      _ = j (q i (t, a)) := hq0 i a ha t ht
  let Aext : Set E3 := S \ (j '' Do rhoN)
  let Cwall : Set E3 := j '' Dc rhoN
  let Utrack : Set E3 := {y | |H y - c| < 3 * delta} \ (j '' Dc (rhoN / 2))
  have hAeq : Aext = j '' (Do rhoN)ᶜ := by
    change S \ (j '' Do rhoN) = j '' (Do rhoN)ᶜ
    rw [← hRange]
    ext y
    constructor
    · rintro ⟨⟨p, rfl⟩, hp⟩
      exact ⟨p, fun hh => hp ⟨p, hh, rfl⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzp⟩
      exact hp ((hji hzp) ▸ hz)
  have hDo : IsOpen (Do rhoN) := (hRadial rhoN hrho (by linarith only [hrho])).1
  have hDc : IsCompact (Dc rhoN) := (hRadial rhoN hrho (by linarith only [hrho])).2.1
  have hAclosed : IsClosed Aext :=
    hAeq.symm ▸ (hDo.isClosed_compl.isCompact.image hj).isClosed
  have hCclosed : IsClosed Cwall := (hDc.image hj).isClosed
  have hhalf : IsCompact (Dc (rhoN / 2)) :=
    (hRadial (rhoN / 2) (half_pos hrho) (by linarith only [hrho])).2.1
  have hUtrack : IsOpen Utrack :=
    (isOpen_lt ((H.continuous.sub continuous_const).abs) continuous_const).sdiff
      (hhalf.image hj).isClosed
  have hDoDc (r : ℝ) : Do r ⊆ Dc r := image_mono (fun s hs => by
    change r2 s < r ^ 2 at hs
    exact hs.le)
  have hsmall : Dc (rhoN / 2) ⊆ Dc rhoN := image_mono (fun s hs => by
    change r2 s ≤ (rhoN / 2) ^ 2 at hs
    change r2 s ≤ rhoN ^ 2
    nlinarith only [hs, sq_nonneg rhoN])
  have hSC : S \ Cwall ⊆ Aext := by
    intro y hy
    exact ⟨hy.1, fun hh => hy.2 ((image_mono (hDoDc rhoN)) hh)⟩
  have hunit : ∀ y ∈ S ∩ Utrack, H (X y) = 1 := by
    rintro y ⟨hy, hp⟩
    obtain ⟨p, rfl⟩ : y ∈ range j := hRange.symm ▸ hy
    exact hXH p hp.1.le (fun hh => hp.2 ⟨p, hDoDc (rhoN / 2) hh, rfl⟩)
  have hsafe : ∀ y ∈ Aext \ Cwall, |H y - c| ≤ 2 * delta → y ∈ Utrack := by
    intro y hy hh
    have hheight : |H y - c| < 3 * delta := by linarith only [hh, hdelta]
    exact ⟨hheight, fun hz => hy.2 ((image_mono hsmall) hz)⟩
  have hwallA (t : ℝ) (ht : |t| ≤ 2 * delta) :
      {y : E3 | y ∈ Aext ∩ Cwall ∧ H y = c + t} =
        range (fun i : Fin 4 => j (q i (t, 0))) := by
    ext y
    constructor
    · rintro ⟨⟨hyA, p, hp, hpy⟩, hyH⟩
      have hpw : p ∈ {z : UnitTwoSphere |
          z ∈ Dc rhoN \ Do rhoN ∧ H0 (j z) = k + d + t} :=
        ⟨⟨hp, fun hpo => hyA.2 ⟨p, hpo, hpy⟩⟩, hpy.symm ▸ hyH⟩
      rw [hwall t ht] at hpw
      obtain ⟨i, hi⟩ := hpw
      exact ⟨i, (congrArg j hi).trans hpy⟩
    · rintro ⟨i, rfl⟩
      have hp : q i (t, 0) ∈ {z : UnitTwoSphere |
          z ∈ Dc rhoN \ Do rhoN ∧ H0 (j z) = k + d + t} := by
        rw [hwall t ht]
        exact mem_range_self i
      refine ⟨⟨⟨hjS (q i (t, 0)), ?_⟩, ⟨q i (t, 0), hp.1.1, rfl⟩⟩, hp.2⟩
      rintro ⟨p, hpo, hpeq⟩
      exact hp.1.2 ((hji hpeq) ▸ hpo)
  have hbarrier := boundedFlow_exterior_level_images X hK hB H S Cwall Aext Utrack
    hAclosed hCclosed hUtrack (fun _ hy => hy.1) hSC c delta hflow hunit hsafe
    (fun i t => j (q i (t, 0))) hwallA
    (fun i s t hs ht => hqflow i 0 (by norm_num) s t hs ht)
  have hE (t : ℝ) : Elevel t = {y : E3 | y ∈ Aext ∧ H y = c + t} := by
    ext y
    change ((y ∈ S ∧ H y = c + t) ∧ y ∉ j '' Do rhoN) ↔
      ((y ∈ S ∧ y ∉ j '' Do rhoN) ∧ H y = c + t)
    exact ⟨fun hy => ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩,
      fun hy => ⟨⟨hy.1.1, hy.2⟩, hy.1.2⟩⟩
  refine ⟨K, B, hK, hB, hS, hcX.isCompact, hXs, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hder, ?_, ?_⟩
  · exact (boundedFlow_contDiff X hK hB hX hcX).comp
      (contDiff_snd.prodMk (contDiff_fst.snd.sub contDiff_fst.fst))
  · change ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E3 =>
      boundedFlow X hK hB p.2 (-(p.1.2 - p.1.1)))
    simpa only [neg_sub, Function.comp_def] using (boundedFlow_contDiff X hK hB hX hcX).comp
      (contDiff_snd.prodMk (contDiff_fst.fst.sub contDiff_fst.snd))
  · intro s t y
    exact ⟨rfl, by change boundedFlow X hK hB y (-(t - s)) = _; rw [neg_sub]⟩
  · intro s y
    change boundedFlow X hK hB y (s - s) = y
    rw [sub_self, boundedFlow_zero]
  · intro s t y
    change HasDerivAt (fun a : ℝ => boundedFlow X hK hB y (a - s))
      (X (boundedFlow X hK hB y (t - s))) t
    simpa only [Function.comp_def, id_eq, one_smul] using
      (boundedFlow_hasDerivAt X hK hB y (t - s)).scomp t ((hasDerivAt_id t).sub_const s)
  · intro s t
    exact ⟨closure_mono (boundedFlow_support_subset X hK hB (t - s)),
      closure_mono (boundedFlow_support_subset X hK hB (-(t - s)))⟩
  · intro s t
    exact ⟨hSimage (t - s), hSimage (-(t - s))⟩
  · intro s t y hy
    have hz : X y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => by
      rcases hy with hy | hy
      · exact (hXs hh).2 hy
      · exact (not_lt_of_ge hy) (hXs hh).1.2)
    exact ⟨boundedFlow_eq_self X hK hB y hz (t - s),
      boundedFlow_eq_self X hK hB y hz (-(t - s))⟩
  · intro i a ha s t hs ht
    refine ⟨hqflow i a ha s t hs ht, ?_⟩
    change boundedFlow X hK hB (j (q i (t, a))) (-(t - s)) = _
    rw [neg_sub]
    exact hqflow i a ha t s ht hs
  · intro s t hs ht
    change (fun y => boundedFlow X hK hB y (t - s)) '' Elevel s = Elevel t ∧
      (fun y => boundedFlow X hK hB y (-(t - s))) '' Elevel t = Elevel s
    rw [hE s, hE t]
    exact hbarrier s t hs ht

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
