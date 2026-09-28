import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceTangentExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M65Boundary

theorem exists_boundary_arc_straightening {c : ℝ → LoopAmbient} {I : Set ℝ} {s : ℝ}
    (hI : IsOpen I) (hs : s ∈ I) (hc : ContDiffOn ℝ ∞ c I) (hder : deriv c s ≠ 0) :
    ∃ (j : Fin 3) (J : Set ℝ) (E : OpenPartialHomeomorph LoopAmbient LoopAmbient),
      IsOpen J ∧ s ∈ J ∧ J ⊆ I ∧ c s ∈ E.source ∧ (0 : LoopAmbient) ∈ E.target ∧
      MapsTo c J E.source ∧ ContDiffOn ℝ ∞ E E.source ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      (∀ t ∈ J, E (c t) = (t - s) • EuclideanSpace.basisFun (Fin 3) ℝ j) ∧
      (∀ y ∈ E.target, s + y j ∈ J ∧
        E.symm y = c (s + y j) +
          (y - y j • EuclideanSpace.basisFun (Fin 3) ℝ j)) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, deriv c s j ≠ 0 := by
    by_contra h
    push Not at h
    apply hder
    ext j
    exact h j
  let b := EuclideanSpace.basisFun (Fin 3) ℝ j
  let pr : LoopAmbient →L[ℝ] ℝ := EuclideanSpace.proj j
  let h := fun t : ℝ => c t j
  have hhc : ContDiffOn ℝ ∞ h I := pr.contDiff.comp_contDiffOn hc
  have hds : deriv h s = deriv c s j :=
    (pr.hasFDerivAt.comp_hasDerivAt s
      (((hc s hs).contDiffAt (hI.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt).deriv
  obtain ⟨e, he, hse, heI, _hene, heinv⟩ :=
    M65StrictTrace.exists_regular_coordinate_inverse hI hs hhc (by rwa [hds])
  let U : Set LoopAmbient := pr ⁻¹' e.target
  let V : Set LoopAmbient := (fun y => s + pr y) ⁻¹' e.source
  let sigma := fun q : LoopAmbient => e.symm (pr q)
  let X := fun q : LoopAmbient => (sigma q - s) • b + (q - c (sigma q))
  let P := fun y : LoopAmbient => c (s + pr y) + (y - pr y • b)
  have hb : b j = 1 := by simp [b, EuclideanSpace.basisFun_apply]
  have hU : IsOpen U := e.open_target.preimage pr.continuous
  have hV : IsOpen V := e.open_source.preimage (continuous_const.add pr.continuous)
  have hsig : ContDiffOn ℝ ∞ sigma U :=
    heinv.comp pr.contDiff.contDiffOn (fun _ hz => hz)
  have hsigmem (q : LoopAmbient) (hq : q ∈ U) : sigma q ∈ e.source := e.map_target hq
  have hcSig : ContDiffOn ℝ ∞ (fun q => c (sigma q)) U :=
    hc.comp hsig (fun q hq => heI (hsigmem q hq))
  have hX : ContDiffOn ℝ ∞ X U :=
    (hsig.sub contDiffOn_const).smul contDiffOn_const |>.add (contDiffOn_id.sub hcSig)
  have hP : ContDiffOn ℝ ∞ P V :=
    (hc.comp (contDiff_const.add pr.contDiff).contDiffOn (fun _ hy => heI hy)).add
      (contDiffOn_id.sub (pr.contDiff.contDiffOn.smul contDiffOn_const))
  have hparam (t : ℝ) (ht : t ∈ e.source) : sigma (c t) = t := by
    change e.symm (h t) = t
    rw [← he]
    exact e.left_inv ht
  have hcoord (q : LoopAmbient) (hq : q ∈ U) : c (sigma q) j = q j := by
    have hh := e.right_inv hq
    change e (e.symm (pr q)) = pr q at hh
    rw [he] at hh
    exact hh
  have hXj (q : LoopAmbient) (hq : q ∈ U) : X q j = sigma q - s := by
    change ((sigma q - s) • b + (q - c (sigma q))) j = _
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      hb, mul_one, hcoord q hq, sub_self, add_zero]
  have hPj (y : LoopAmbient) : P y j = c (s + pr y) j := by
    change (c (s + pr y) + (y - pr y • b)) j = _
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hb, mul_one]
    change c (s + pr y) j + (y j - y j) = _
    ring
  have hXV : MapsTo X U V := by
    intro q hq
    change s + X q j ∈ e.source
    rw [hXj q hq, add_sub_cancel]
    exact hsigmem q hq
  have hPU : MapsTo P V U := by
    intro y hy
    change P y j ∈ e.target
    rw [hPj]
    change h (s + pr y) ∈ e.target
    rw [← he]
    exact e.map_source hy
  have hPX (q : LoopAmbient) (hq : q ∈ U) : P (X q) = q := by
    change c (s + X q j) + (X q - X q j • b) = q
    rw [hXj q hq, add_sub_cancel]
    dsimp only [X]
    abel
  have hXP (y : LoopAmbient) (hy : y ∈ V) : X (P y) = y := by
    have hsigP : sigma (P y) = s + pr y := by
      change e.symm (P y j) = _
      rw [hPj]
      change e.symm (h (s + pr y)) = _
      rw [← he]
      exact e.left_inv hy
    change (sigma (P y) - s) • b + (P y - c (sigma (P y))) = y
    rw [hsigP, add_sub_cancel_left]
    dsimp only [P]
    abel
  let E : OpenPartialHomeomorph LoopAmbient LoopAmbient := {
    toPartialEquiv := {
      toFun := X
      invFun := P
      source := U
      target := V
      map_source' := hXV
      map_target' := hPU
      left_inv' := hPX
      right_inv' := hXP }
    open_source := hU
    open_target := hV
    continuousOn_toFun := hX.continuousOn
    continuousOn_invFun := hP.continuousOn }
  have hcU : MapsTo c e.source U := by
    intro t ht
    change h t ∈ e.target
    rw [← he]
    exact e.map_source ht
  refine ⟨j, e.source, E, e.open_source, hse, heI, hcU hse, ?_, hcU, hX, hP, ?_, ?_⟩
  · change s + pr 0 ∈ e.source
    simpa only [map_zero, add_zero] using hse
  · intro t ht
    change (sigma (c t) - s) • b + (c t - c (sigma (c t))) = _
    rw [hparam t ht, sub_self, add_zero]
  · intro y hy
    exact ⟨hy, rfl⟩

end PoincareConjecture.M65Boundary
