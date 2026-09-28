


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CapTransversality







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Triangles

private theorem exists_sign_radius {f : ℝ × ℝ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0)
    (hdf : HasFDerivAt f (ContinuousLinearMap.fst ℝ ℝ ℝ) 0)
    (hzero : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0) :
    ∃ δ > 0, ∀ r t : ℝ, |r| < δ → |t| < δ →
      (0 < f (r, t) ↔ 0 < r) ∧ (f (r, t) = 0 ↔ r = 0) ∧
        (0 ≤ f (r, t) ↔ 0 ≤ r) := by
  let K : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p => (f p.2, p.2.2)
  have hK : ContDiffAt ℝ 1 K (0, (0, 0)) :=
    (hf.comp (0, (0, 0)) contDiffAt_snd).prodMk contDiffAt_snd.snd
  have hdS : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)) := hasFDerivAt_snd
  have hdK : HasFDerivAt K (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)) := by
    convert! (hdf.comp (0, (0, 0)) hdS).prodMk hdS.snd using 1
  have haxes : ∀ᶠ p in 𝓝 ((0 : ℝ), ((0 : ℝ), (0 : ℝ))),
      (p.2.1 = 0 → (K p).1 = 0) ∧ (p.2.2 = 0 → (K p).2 = 0) := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with p hp
    exact ⟨hp, id⟩
  obtain ⟨δ, hδ, hsign⟩ := Poincare.Analysis.exists_quadrant_preserving_radius hK hdK haxes
  exact ⟨δ, hδ, fun r t hr ht => (hsign 0 r t (by simpa using hδ) hr ht).1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



private theorem exists_affine_sign_radius {g : E → ℝ} {p v d : E}
    (hg : ContDiffAt ℝ 1 g p)
    (hv : fderiv ℝ g p v = 1) (hd : fderiv ℝ g p d = 0)
    (hzero : ∀ᶠ t in 𝓝 (0 : ℝ), g (p + t • d) = 0) :
    ∃ δ > 0, ∀ r t : ℝ, |r| < δ → |t| < δ →
      (0 < g (p + r • v + t • d) ↔ 0 < r) ∧
        (g (p + r • v + t • d) = 0 ↔ r = 0) ∧
        (0 ≤ g (p + r • v + t • d) ↔ 0 ≤ r) := by
  let H : ℝ × ℝ → E := fun q => p + q.1 • v + q.2 • d
  have hH : ContDiff ℝ ∞ H := contDiff_const.add
    (contDiff_fst.smul contDiff_const) |>.add (contDiff_snd.smul contDiff_const)
  have hH0 : H 0 = p := by simp [H]
  have hcomp : ContDiffAt ℝ 1 (g ∘ H) 0 := by
    apply ContDiffAt.comp _ _ (hH.of_le (by simp)).contDiffAt
    simpa only [hH0] using hg
  have hdH : HasFDerivAt H
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight d) 0 := by
    have hfst : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := hasFDerivAt_snd
    convert! ((hasFDerivAt_const p (0 : ℝ × ℝ)).add
      (hfst.smul_const v)).add (hsnd.smul_const d) using 1
    simp
  have hdg : HasFDerivAt g (fderiv ℝ g p) (H 0) := by
    simpa only [hH0] using hg.differentiableAt_one.hasFDerivAt
  have hdf : HasFDerivAt (g ∘ H) (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := by
    have heq : (fderiv ℝ g p).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight d) =
        ContinuousLinearMap.fst ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [hv, hd]
    convert! hdg.comp 0 hdH using 1
    exact heq.symm
  have hz : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → (g ∘ H) q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with q hq hq0
    simpa [H, hq0] using hq
  exact exists_sign_radius hcomp hdf hz





theorem exists_cap_chord_separation
    (F : OpenPartialHomeomorph (ℝ × ℝ) E)
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t : ℝ, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε)) (terminal : Bool) :
    let a := if terminal then F (0, ε) else F (ε, 0)
    let v := if terminal then deriv (fun t : ℝ => F (0, t)) ε
      else deriv (fun s : ℝ => F (s, 0)) ε
    let d := if terminal then F (ε, 0) - F (0, ε) else F (0, ε) - F (ε, 0)
    ∃ δ > 0, ∀ r t : ℝ, |r| < δ → |t| < δ →
      (0 < capExcess F ε (a + r • v + t • d) ↔ 0 < r) ∧
      (capExcess F ε (a + r • v + t • d) = 0 ↔ r = 0) ∧
      (0 ≤ capExcess F ε (a + r • v + t • d) ↔ 0 ≤ r) ∧
      (0 < r → a + r • v + t • d ∉
        F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) := by
  let q₀ : ℝ × ℝ := if terminal then (0, ε) else (ε, 0)
  let a := F q₀
  let v := if terminal then deriv (fun t : ℝ => F (0, t)) ε
    else deriv (fun s : ℝ => F (s, 0)) ε
  let d := if terminal then F (ε, 0) - F (0, ε) else F (0, ε) - F (ε, 0)
  have hq₀ : q₀ ∈ F.source := by
    apply hsource
    cases terminal <;> simp [q₀, hε.le]
  have ha : a = if terminal then F (0, ε) else F (ε, 0) := by
    cases terminal <;> rfl
  have hcap : ContDiffAt ℝ 1 (capExcess F ε) a := by
    have hInv := ((hI a (F.map_source hq₀)).contDiffAt
      (F.open_target.mem_nhds (F.map_source hq₀))).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
    exact (hInv.fst.add hInv.snd).sub contDiffAt_const
  obtain ⟨-, -, -, -, hv₁, hv₂, hd₁, hd₂⟩ :=
    cap_endpoint_transversality F hF hI hε hsource (fun t _ => hchord t)
  have hv : fderiv ℝ (capExcess F ε) a v = 1 := by
    cases terminal
    · exact hv₁
    · exact hv₂
  have hd : fderiv ℝ (capExcess F ε) a d = 0 := by
    cases terminal
    · exact hd₁
    · exact hd₂
  let path : ℝ → ℝ × ℝ := fun t =>
    if terminal then (t * ε, (1 - t) * ε) else ((1 - t) * ε, t * ε)
  have hpath : Continuous path := by cases terminal <;> dsimp [path] <;> fun_prop
  have hpath0 : path 0 = q₀ := by cases terminal <;> simp [path, q₀]
  have hpathsource : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ F.source :=
    hpath.continuousAt.eventually (F.open_source.mem_nhds (by rwa [hpath0]))
  have hline (t : ℝ) : F (path t) = a + t • d := by
    cases terminal
    · dsimp [path, a, q₀, d]
      rw [hchord]
      module
    · dsimp [path, a, q₀, d]
      have h := hchord (1 - t)
      simp only [sub_sub_cancel] at h
      rw [h]
      module
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ), capExcess F ε (a + t • d) = 0 := by
    filter_upwards [hpathsource] with t ht
    rw [← hline, capExcess, F.left_inv ht]
    cases terminal <;> dsimp [path] <;> ring
  obtain ⟨δ, hδ, hsign⟩ := exists_affine_sign_radius hcap hv hd hzero
  dsimp only
  rw [← ha]
  refine ⟨δ, hδ, ?_⟩
  intro r t hr ht
  obtain ⟨hpos, heq, hnonneg⟩ := hsign r t hr ht
  refine ⟨hpos, heq, hnonneg, ?_⟩
  intro hrpos hmem
  exact (not_lt_of_ge (capExcess_nonpos_on_cap F hsource _ hmem)) (hpos.mpr hrpos)



theorem exists_cap_chord_separator
    (F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t : ℝ, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε)) (terminal : Bool) :
    let a := if terminal then F (0, ε) else F (ε, 0)
    let v := if terminal then deriv (fun t : ℝ => F (0, t)) ε
      else deriv (fun s : ℝ => F (s, 0)) ε
    let d := if terminal then F (ε, 0) - F (0, ε) else F (0, ε) - F (ε, 0)
    ∃ (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (W : Set (EuclideanSpace ℝ (Fin 2))),
      ℓ v = 1 ∧ ℓ d = 0 ∧ IsOpen W ∧ a ∈ W ∧
      (∀ z ∈ W, (0 < capExcess F ε z ↔ 0 < ℓ (z - a)) ∧
        (capExcess F ε z = 0 ↔ ℓ (z - a) = 0)) ∧
      ∀ z ∈ W ∩ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε},
        ℓ (z - a) ≤ 0 := by
  let a := if terminal then F (0, ε) else F (ε, 0)
  let v := if terminal then deriv (fun t : ℝ => F (0, t)) ε
    else deriv (fun s : ℝ => F (s, 0)) ε
  let d := if terminal then F (ε, 0) - F (0, ε) else F (0, ε) - F (ε, 0)
  have hind : LinearIndependent ℝ (![v, d] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    obtain ⟨h₁, h₂, -⟩ := cap_endpoint_transversality F hF hI hε hsource
      (fun t _ => hchord t)
    cases terminal
    · exact h₁
    · exact h₂
  let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  let L := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    B.equivFun.toContinuousLinearEquiv.symm
  have hL (q : ℝ × ℝ) : L q = q.1 • v + q.2 • d := by
    change B.equivFun.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm q) = _
    rw [Module.Basis.equivFun_symm_apply]
    simp [B, Fin.sum_univ_succ, coe_basisOfLinearIndependentOfCardEqFinrank]
  obtain ⟨δ, hδ, hsign⟩ := exists_cap_chord_separation F hF hI hε hsource hchord terminal
  let ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.symm.toContinuousLinearMap
  let W : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | |(L.symm (z - a)).1| < δ ∧ |(L.symm (z - a)).2| < δ}
  have hW : IsOpen W := by
    change IsOpen ({z | |(L.symm (z - a)).1| < δ} ∩
      {z | |(L.symm (z - a)).2| < δ})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have ha : a ∈ W := by simp [W, hδ]
  have heq (z : EuclideanSpace ℝ (Fin 2)) :
      a + (L.symm (z - a)).1 • v + (L.symm (z - a)).2 • d = z := by
    rw [add_assoc, ← hL, L.apply_symm_apply]
    abel
  refine ⟨ℓ, W, ?_, ?_, hW, ha, ?_, ?_⟩
  · have hv : L (1, 0) = v := by simp [hL]
    change (L.symm v).1 = 1
    rw [← hv, L.symm_apply_apply]
  · have hd : L (0, 1) = d := by simp [hL]
    change (L.symm d).1 = 0
    rw [← hd, L.symm_apply_apply]
  · intro z hz
    have hs := hsign (L.symm (z - a)).1 (L.symm (z - a)).2 hz.1 hz.2
    change (0 < capExcess F ε z ↔ 0 < (L.symm (z - a)).1) ∧
      (capExcess F ε z = 0 ↔ (L.symm (z - a)).1 = 0)
    change (0 < capExcess F ε (a + _ • v + _ • d) ↔ _) ∧ _ at hs
    rw [heq] at hs
    exact ⟨hs.1, hs.2.1⟩
  · intro z hz
    have hs := hsign (L.symm (z - a)).1 (L.symm (z - a)).2 hz.1.1 hz.1.2
    change (0 < capExcess F ε (a + _ • v + _ • d) ↔ _) ∧ _ at hs
    rw [heq] at hs
    exact le_of_not_gt (fun h => (not_lt_of_ge
      (capExcess_nonpos_on_cap F hsource z hz.2)) (hs.1.mpr h))

end Poincare.Topology.Plane.Triangles
