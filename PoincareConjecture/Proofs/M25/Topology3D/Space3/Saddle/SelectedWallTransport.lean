import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ExteriorFlowBarrier
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow
import Mathlib.Tactic.Tauto








set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace NNReal Topology Matrix

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_selected_wall_transport
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hdeltaR : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target)
    (hcore : ∀ q : UnitTwoSphere,
      |⟪(u : E3), psi (q, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → q ∈ D.sourceCore)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c : ℝ := H (j D.point)
    let S : Set E3 := Set.range j
    let rho : ℝ := 5 * R / 8
    let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
    let Do : ℝ → Set UnitTwoSphere := fun r =>
      D.morse.symm '' {s | r2 s < r ^ 2}
    let Dc : ℝ → Set UnitTwoSphere := fun r =>
      D.morse.symm '' {s | r2 s ≤ r ^ 2}
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
      (sx i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
        sy i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
    let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere :=
      fun i p => D.morse.symm (N (xi i p))
    let Elevel : ℝ → Set E3 := fun t =>
      (S ∩ {y | H y = c + t}) \ (j '' Do rho)
    ∃ (F : E3 → E3) (K L : ℝ≥0)
      (hK : LipschitzWith K F) (hL : ∀ y, ‖F y‖ ≤ L)
      (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F),
    let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
      fun t => boundedFlowDiffeomorph F hK hL hF hcF t
    ∃ C : Set E3,
      IsCompact C ∧ tsupport F ⊆ C ∧
      C ⊆ ((psi '' (Set.univ ×ˢ Set.Ioo (-1) 1)) ∩
        {y : E3 | |H y - c| < 4 * delta}) \ (j '' Dc (rho / 4)) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
      (∀ t : ℝ, ∀ y : E3,
        Phi t y = boundedFlow F hK hL y t ∧
        (Phi t).symm y = boundedFlow F hK hL y (-t)) ∧
      (∀ t : ℝ,
        tsupport (fun y : E3 => Phi t y - y) ⊆ C ∧
        tsupport (fun y : E3 => (Phi t).symm y - y) ⊆ C) ∧
      (∀ t : ℝ, Phi t '' S = S ∧ (Phi t).symm '' S = S) ∧
      (∀ t : ℝ, ∀ y : E3,
        (y ∈ j '' Dc (rho / 4) ∨ 4 * delta ≤ |H y - c|) →
          Phi t y = y ∧ (Phi t).symm y = y) ∧
      (∀ p : UnitTwoSphere, |H (j p) - c| ≤ 3 * delta →
        p ∉ Do (rho / 2) → H (F (j p)) = 1) ∧
      IsOpen (Do rho) ∧ IsCompact (Dc rho) ∧
      closure (Do rho) = Dc rho ∧
      (∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ t : ℝ, |t| ≤ 2 * delta →
          q i (t, a) ∈ D.morse.source ∧
          H (j (q i (t, a))) = c + t ∧
          r2 (D.morse (q i (t, a))) = rho ^ 2 * (1 + a) ^ 2) ∧
      (∀ t : ℝ, |t| ≤ 2 * delta →
        {p : UnitTwoSphere | p ∈ Dc rho \ Do rho ∧ H (j p) = c + t} =
          Set.range (fun i : Fin 4 => q i (t, 0))) ∧
      (∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          Phi (t - s) (j (q i (s, a))) = j (q i (t, a))) ∧
      ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
        Phi (t - s) '' Elevel s = Elevel t ∧
        (Phi (t - s)).symm '' Elevel t = Elevel s := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let S : Set E3 := range j
  let rho : ℝ := 5 * R / 8
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Do : ℝ → Set UnitTwoSphere := fun r => D.morse.symm '' {s | r2 s < r ^ 2}
  let Dc : ℝ → Set UnitTwoSphere := fun r => D.morse.symm '' {s | r2 s ≤ r ^ 2}
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
    (sx i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
      sy i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
  let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere := fun i p => D.morse.symm (N (xi i p))
  let Elevel : ℝ → Set E3 := fun t => (S ∩ {y | H y = c + t}) \ (j '' Do rho)
  let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
  obtain ⟨f, F, hf, hfpsi, hF, hFc, hFs, hFf, hFH, hDo, hDc, hcl, hq, hwall, hder⟩ :=
    exists_saddle_selected_wall_field psi hpsi u D R delta hR hdelta hdeltaR hmorse hcore N hN
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds F hF hFc
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph F hK hL hF hFc t
  have hform (t : ℝ) (y : E3) : Phi t y = boundedFlow F hK hL y t ∧
      (Phi t).symm y = boundedFlow F hK hL y (-t) := ⟨rfl, rfl⟩
  have hj := (collar_central_contMDiff psi hpsi).continuous
  have hji : Injective j := by
    intro p z hpz
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpz)
  have hU : IsOpen U := collar_image_open psi hpsi
  have hjU (p : UnitTwoSphere) : j p ∈ U :=
    ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hzero (y : E3) (hy : y ∉ U) : F y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hy (hFs hh).1.1)
  have hflow : ∀ y ∈ S, ∀ t : ℝ, boundedFlow F hK hL y t ∈ S := by
    rintro y ⟨p, rfl⟩ t
    have hstay := boundedFlow_mapsTo_set F hK hL hzero t (hjU p)
    have hint := boundedFlow_preserves_firstIntegral F hK hL hzero f
      (fun z hz => (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      (fun z _ => hFf z) (j p) (hjU p) t
    have hfv : f (boundedFlow F hK hL (j p) t) = 0 :=
      hint.trans (hfpsi (p, 0) ⟨mem_univ _, by norm_num⟩)
    obtain ⟨⟨z, r⟩, hzr, heq⟩ := hstay
    have hr : r = 0 := (hfpsi (z, r) hzr).symm.trans ((congrArg f heq).trans hfv)
    subst r
    exact ⟨z, heq⟩
  have hSimage (t : ℝ) : (fun y => boundedFlow F hK hL y t) '' S = S := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact hflow z hz t
    · intro y hy
      exact ⟨boundedFlow F hK hL y (-t), hflow y hy (-t),
        by simpa only [neg_neg] using boundedFlow_neg F hK hL y (-t)⟩
  have hflowc (y : E3) : Continuous (boundedFlow F hK hL y) :=
    continuous_iff_continuousAt.mpr (fun t => (boundedFlow_hasDerivAt F hK hL y t).continuousAt)
  have hq0 (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (t : ℝ) (ht : |t| ≤ 2 * delta) :
      boundedFlow F hK hL (j (q i (0, a))) t = j (q i (t, a)) := by
    have hc : ContinuousOn (fun v : ℝ => j (q i (v, a))) (Icc (-(2 * delta)) (2 * delta)) :=
      fun v hv => (hder i a ha v (abs_le.mpr hv)).continuousAt.continuousWithinAt
    have hu := ODE_solution_unique_of_mem_Icc (v := fun _ : ℝ => F) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-(2 * delta)) (2 * delta) from ⟨by linarith, by linarith⟩)
      (hflowc (j (q i (0, a)))).continuousOn
      (fun v _ => boundedFlow_hasDerivAt F hK hL (j (q i (0, a))) v)
      (fun _ _ => mem_univ _) hc
      (fun v hv => hder i a ha v (abs_le.mpr ⟨hv.1.le, hv.2.le⟩))
      (fun _ _ => mem_univ _) (boundedFlow_zero F hK hL (j (q i (0, a))))
    exact hu (abs_le.mp ht)
  have hqflow (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (s t : ℝ)
      (hs : |s| ≤ 2 * delta) (ht : |t| ≤ 2 * delta) :
      boundedFlow F hK hL (j (q i (s, a))) (t - s) = j (q i (t, a)) := by
    calc
      _ = boundedFlow F hK hL (boundedFlow F hK hL (j (q i (0, a))) s) (t - s) := by
        rw [hq0 i a ha s hs]
      _ = boundedFlow F hK hL (j (q i (0, a))) t := by
        rw [← boundedFlow_add]
        congr 1
        ring
      _ = j (q i (t, a)) := hq0 i a ha t ht
  let Aext : Set E3 := S \ (j '' Do rho)
  let Cwall : Set E3 := j '' Dc rho
  let Utrack : Set E3 := {y | |H y - c| < 3 * delta} \ (j '' Dc (rho / 2))
  have hAeq : Aext = j '' (Do rho)ᶜ := by
    ext y
    constructor
    · rintro ⟨⟨p, rfl⟩, hp⟩
      exact ⟨p, fun hh => hp ⟨p, hh, rfl⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨p, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzp⟩
      exact hp ((hji hzp) ▸ hz)
  have hAclosed : IsClosed Aext := hAeq.symm ▸ (hDo.isClosed_compl.isCompact.image hj).isClosed
  have hCclosed : IsClosed Cwall := (hDc.image hj).isClosed
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hhalf : IsCompact (Dc (rho / 2)) := by
    have htarget : {s : ℝ × ℝ | r2 s ≤ (rho / 2) ^ 2} ⊆ D.morse.target := by
      intro s hs
      apply hmorse
      change r2 s < (2 * R) ^ 2
      dsimp [r2, rho] at hs
      dsimp [r2]
      nlinarith [sq_pos_of_pos hR]
    exact (morseRadialDisc_geometry (rho / 2) (by positivity)).2.1.image_of_continuousOn
      (D.morse.symm.continuousOn.mono htarget)
  have hUtrack : IsOpen Utrack :=
    (isOpen_lt ((H.continuous.sub continuous_const).abs) continuous_const).sdiff
      (hhalf.image hj).isClosed
  have hDoDc (r : ℝ) : Do r ⊆ Dc r := image_mono (fun s hs => by
    change r2 s < r ^ 2 at hs
    exact hs.le)
  have hsmall : Dc (rho / 2) ⊆ Dc rho := image_mono (fun s hs => by
    change r2 s ≤ (rho / 2) ^ 2 at hs
    change r2 s ≤ rho ^ 2
    nlinarith [sq_nonneg rho])
  have hSC : S \ Cwall ⊆ Aext := by
    intro y hy
    exact ⟨hy.1, fun hh => hy.2 ((image_mono (hDoDc rho)) hh)⟩
  have hunit : ∀ y ∈ S ∩ Utrack, H (F y) = 1 := by
    rintro y ⟨⟨p, rfl⟩, hp⟩
    exact hFH p hp.1.le (fun hh => hp.2 ⟨p, hDoDc (rho / 2) hh, rfl⟩)
  have hsafe : ∀ y ∈ Aext \ Cwall, |H y - c| ≤ 2 * delta → y ∈ Utrack := by
    intro y hy hh
    have hheight : |H y - c| < 3 * delta := by linarith
    exact ⟨hheight, fun hz => hy.2 ((image_mono hsmall) hz)⟩
  have hwallA (t : ℝ) (ht : |t| ≤ 2 * delta) :
      {y : E3 | y ∈ Aext ∩ Cwall ∧ H y = c + t} = range (fun i => j (q i (t, 0))) := by
    ext y
    constructor
    · rintro ⟨⟨hyA, p, hp, hpy⟩, hyH⟩
      have hpw : p ∈ {z : UnitTwoSphere | z ∈ Dc rho \ Do rho ∧ H (j z) = c + t} :=
        ⟨⟨hp, fun hpo => hyA.2 ⟨p, hpo, hpy⟩⟩, hpy.symm ▸ hyH⟩
      rw [hwall t ht] at hpw
      obtain ⟨i, hi⟩ := hpw
      exact ⟨i, (congrArg j hi).trans hpy⟩
    · rintro ⟨i, rfl⟩
      have hp : q i (t, 0) ∈ {z : UnitTwoSphere | z ∈ Dc rho \ Do rho ∧ H (j z) = c + t} := by
        rw [hwall t ht]
        exact mem_range_self i
      refine ⟨⟨⟨⟨q i (t, 0), rfl⟩, ?_⟩, ⟨q i (t, 0), hp.1.1, rfl⟩⟩, hp.2⟩
      rintro ⟨p, hpo, hpeq⟩
      exact hp.1.2 ((hji hpeq) ▸ hpo)
  have hbarrier := boundedFlow_exterior_level_images F hK hL H S Cwall Aext Utrack
    hAclosed hCclosed hUtrack (fun _ hy => hy.1) hSC c delta hflow hunit hsafe
    (fun i t => j (q i (t, 0))) hwallA (fun i s t hs ht => hqflow i 0 (by norm_num) s t hs ht)
  have hE (t : ℝ) : Elevel t = {y : E3 | y ∈ Aext ∧ H y = c + t} := by
    ext y
    change ((y ∈ S ∧ H y = c + t) ∧ y ∉ j '' Do rho) ↔
      ((y ∈ S ∧ y ∉ j '' Do rho) ∧ H y = c + t)
    tauto
  refine ⟨F, K, L, hK, hL, hF, hFc, tsupport F, hFc.isCompact, Subset.rfl, hFs,
    ?_, ?_, hform, ?_, ?_, ?_, hFH, hDo, hDc, hcl, hq, hwall, ?_, ?_⟩
  · exact (boundedFlow_contDiff F hK hL hF hFc).comp (contDiff_snd.prodMk contDiff_fst)
  · exact (boundedFlow_contDiff F hK hL hF hFc).comp (contDiff_snd.prodMk contDiff_fst.neg)
  · intro t
    exact ⟨closure_mono (boundedFlow_support_subset F hK hL t),
      closure_mono (boundedFlow_support_subset F hK hL (-t))⟩
  · intro t
    exact ⟨hSimage t, hSimage (-t)⟩
  · intro t y hy
    have hz : F y = 0 := image_eq_zero_of_notMem_tsupport (fun hh => by
      rcases hy with hy | hy
      · exact (hFs hh).2 hy
      · exact (not_lt_of_ge hy) (hFs hh).1.2)
    exact ⟨boundedFlow_eq_self F hK hL y hz t, boundedFlow_eq_self F hK hL y hz (-t)⟩
  · intro i a ha s t hs ht
    exact hqflow i a ha s t hs ht
  · intro s t hs ht
    change (fun y => boundedFlow F hK hL y (t - s)) '' Elevel s = Elevel t ∧
      (fun y => boundedFlow F hK hL y (-(t - s))) '' Elevel t = Elevel s
    rw [hE s, hE t]
    exact hbarrier s t hs ht

end PoincareConjecture.M25.Topology3D
