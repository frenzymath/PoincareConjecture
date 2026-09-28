import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField

set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal Manifold

namespace PoincareConjecture.M25.Topology3D

theorem saddle_common_middle_exterior_images
    (u : UnitTwoSphere) (c delta : ℝ) (hdelta : 0 < delta)
    (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (X : Fin 2 → E3 → E3) (S : Fin 2 → Set E3) :
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let b : Fin 2 → ℝ × E2 → E2 := fun j p =>
      fderiv ℝ gRef.symm (gRef p.2)
        (pi (X j (L.symm (gRef p.2, c + p.1))))
    let E : Fin 2 → ℝ → Set E2 := fun j t =>
      {x : E2 | L.symm (gRef x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}
    let Ext : Fin 2 → ℝ → Set E3 := fun j t =>
      L.symm '' ((gRef '' E j t) ×ˢ ({c + t} : Set ℝ))
    ∀ (T : Fin 2 → ℝ → ℝ →
        Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (_hTself : ∀ (j : Fin 2) (s : ℝ) (y : E3), T j s s y = y)
      (_hTtrack : ∀ (j : Fin 2) (s : ℝ), |s| < 2 * delta →
        ∀ y ∈ Ext j s, ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun a : ℝ => T j s a y) (X j (T j s t y)) t)
      (_hTimage : ∀ (j : Fin 2) (s t : ℝ),
        |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          (T j s t) '' Ext j s = Ext j t ∧
          (T j s t).symm '' Ext j t = Ext j s)
      (W : Fin 2 → ℝ × E2 → E2)
      (hW : ∀ j : Fin 2,
        ContDiff ℝ ∞ (W j) ∧ HasCompactSupport (W j))
      (KW LW : Fin 2 → ℝ≥0)
      (hKW : ∀ j : Fin 2, LipschitzWith (KW j) (clockField (W j)))
      (hLW : ∀ (j : Fin 2) (p : ℝ × E2),
        ‖clockField (W j) p‖ ≤ LW j)
      (_hEq : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
        EqOn (fun x : E2 => W j (t, x)) (fun x => b j (t, x)) (E j t)),
      let Phi : Fin 2 → ℝ → ℝ →
          Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
        fun j => clockEvolutionDiffeomorph (W j) (hKW j) (hLW j)
          (hW j).1 (hW j).2
      ∀ (j : Fin 2) (t : ℝ), |t| ≤ delta →
        (Phi j 0 t) '' E j 0 = E j t ∧
        (Phi j 0 t).symm '' E j t = E j 0 := by
  dsimp only
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let b : Fin 2 → ℝ × E2 → E2 := fun j p =>
    fderiv ℝ gRef.symm (gRef p.2)
      (pi (X j (L.symm (gRef p.2, c + p.1))))
  let E : Fin 2 → ℝ → Set E2 := fun j t =>
    {x : E2 | L.symm (gRef x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}
  let Ext : Fin 2 → ℝ → Set E3 := fun j t =>
    L.symm '' ((gRef '' E j t) ×ˢ ({c + t} : Set ℝ))
  intro T hTself hTtrack hTimage W hW KW LW hKW hLW hEq
  let Phi (j : Fin 2) :=
    clockEvolutionDiffeomorph (W j) (hKW j) (hLW j) (hW j).1 (hW j).2
  let pr : E3 → E2 := fun y => gRef.symm (pi y)
  let lift : ℝ → E2 → E3 := fun t x => L.symm (gRef x, c + t)
  have hpi (x : E2) (z : ℝ) : pi (L.symm (x, z)) = x := by
    simp only [pi, L, horizontalBandProjection_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hpr (t : ℝ) (x : E2) : pr (lift t x) = x := by
    dsimp only [pr, lift]
    rw [hpi, gRef.symm_apply_apply]
  have hLift (j : Fin 2) (t : ℝ) (x : E2) (hx : x ∈ E j t) :
      lift t x ∈ Ext j t :=
    ⟨(gRef x, c + t), ⟨⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  have hExt (j : Fin 2) (t : ℝ) (y : E3) (hy : y ∈ Ext j t) :
      pr y ∈ E j t ∧ lift t (pr y) = y := by
    rcases hy with ⟨⟨z, a⟩, ⟨⟨x, hx, rfl⟩, ha⟩, rfl⟩
    have ha' : a = c + t := ha
    subst a
    change pr (lift t x) ∈ E j t ∧ lift t (pr (lift t x)) = lift t x
    rw [hpr]
    exact ⟨hx, rfl⟩
  have hzero : |(0 : ℝ)| < 2 * delta := by
    simpa only [abs_zero] using mul_pos (by norm_num : (0 : ℝ) < 2) hdelta
  have hAmbient (j : Fin 2) (y : E3) (hy : y ∈ Ext j 0)
      (t : ℝ) (ht : |t| < 2 * delta) : T j 0 t y ∈ Ext j t := by
    have hImage : (T j 0 t) '' Ext j 0 = Ext j t :=
      (hTimage j 0 t hzero.le ht.le).1
    rw [← hImage]
    exact ⟨y, hy, rfl⟩
  have hTrack (j : Fin 2) (x : E2) (hx : x ∈ E j 0)
      (t : ℝ) (ht : |t| < 2 * delta) :
      Phi j 0 t x = pr (T j 0 t (lift 0 x)) := by
    let gamma : ℝ → E2 := fun a => pr (T j 0 a (lift 0 x))
    have hmem (a : ℝ) (ha : |a| < 2 * delta) :
        gamma a ∈ E j a ∧ lift a (gamma a) = T j 0 a (lift 0 x) :=
      hExt j a _ (hAmbient j _ (hLift j 0 x hx) a ha)
    have hd (a : ℝ) (ha : a ∈ Ioo (-2 * delta) (2 * delta)) :
        HasDerivAt gamma (W j (a, gamma a)) a := by
      have ha' : |a| < 2 * delta := abs_lt.mpr
        ⟨by linarith only [ha.1], ha.2⟩
      have hdT := hTtrack j 0 hzero (lift 0 x) (hLift j 0 x hx) a ha'
      have hdP := pi.hasFDerivAt.comp_hasDerivAt a hdT
      have hdG := (gRef.symm.contDiff.differentiable (by simp)
        (pi (T j 0 a (lift 0 x)))).hasFDerivAt.comp_hasDerivAt a hdP
      have hrec := (hmem a ha').2
      have hp : pi (T j 0 a (lift 0 x)) = gRef (gamma a) := by
        rw [← hrec]
        exact hpi _ _
      have hvelocity : W j (a, gamma a) = b j (a, gamma a) :=
        hEq j a ha' (hmem a ha').1
      rw [hvelocity]
      change HasDerivAt gamma
        (fderiv ℝ gRef.symm (gRef (gamma a))
          (pi (X j (lift a (gamma a))))) a
      rw [hrec, ← hp]
      simpa only [gamma, pr, Function.comp_def] using hdG
    have hgamma0 : gamma 0 = x := by
      dsimp only [gamma]
      rw [hTself, hpr]
    have hzeroI : (0 : ℝ) ∈ Ioo (-2 * delta) (2 * delta) :=
      ⟨by linarith only [hdelta], by linarith only [hdelta]⟩
    have htI : t ∈ Ioo (-2 * delta) (2 * delta) :=
      ⟨by linarith only [(abs_lt.mp ht).1], (abs_lt.mp ht).2⟩
    have htrack := clockEvolution_tracks (W j) (hKW j) (hLW j) gamma hzeroI hd htI
    change clockEvolution (W j) (hKW j) (hLW j) 0 t x = gamma t
    simpa only [hgamma0] using htrack
  intro j t ht
  change (Phi j 0 t) '' E j 0 = E j t ∧ (Phi j 0 t).symm '' E j t = E j 0
  have ht' : |t| < 2 * delta := by linarith only [ht, hdelta]
  have hForward : (Phi j 0 t) '' E j 0 = E j t := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [hTrack j x hx t ht']
      exact (hExt j t _ (hAmbient j _ (hLift j 0 x hx) t ht')).1
    · intro x hx
      let y0 := (T j 0 t).symm (lift t x)
      have hy0 : y0 ∈ Ext j 0 := by
        have hImage : (T j 0 t).symm '' Ext j t = Ext j 0 :=
          (hTimage j 0 t hzero.le ht'.le).2
        rw [← hImage]
        exact ⟨lift t x, hLift j t x hx, rfl⟩
      have hx0 := hExt j 0 y0 hy0
      refine ⟨pr y0, hx0.1, ?_⟩
      rw [hTrack j (pr y0) hx0.1 t ht', hx0.2]
      dsimp only [y0]
      rw [(T j 0 t).apply_symm_apply]
      exact hpr t x
  refine ⟨hForward, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [← hForward] at hy
    rcases hy with ⟨z, hz, rfl⟩
    simpa only [(Phi j 0 t).symm_apply_apply] using hz
  · intro x hx
    refine ⟨Phi j 0 t x, ?_, (Phi j 0 t).symm_apply_apply x⟩
    rw [← hForward]
    exact ⟨x, hx, rfl⟩

end PoincareConjecture.M25.Topology3D
