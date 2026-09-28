import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedPeriodSpectralApproximants
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonAmbientSpectralFamily
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PrescribedNormalApproximationSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "StateV" => State ((ℤ × Fin 2) × ι)

theorem exists_common_normal_approximants
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {U : Set W} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {γ : ℝ → M} (hγp : Function.Periodic γ L)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    (hunit : ∀ x, curveSpeed F (fun y _ => γ y) a x = 1)
    {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (w : StateV) (wn : ℕ → StateV) (m : ℕ → ℝ)
        (u : StateV → ForcingSpace ((ℤ × Fin 2) × ι) T) (ψ : ℕ → ℝ → ℝ → ℝ),
        let V := fun z => initialResponseTrace lambda z hT.le (u z)
        let q := initialResponseCurve (L := L) hT.le w (u w)
        let qn := fun j => initialResponseCurve (L := L) hT.le (wn j) (u (wn j))
        let c0 := fun x => e (γ x)
        let S := T / 4
        let κ := L / curvePeriod
        let A := fun j t x => ambientCurvePrincipal F ρ (a + t) (qn j t x) (deriv (qn j t) x)
        let cn := fun j x t => ρ (qn j (t - a) (ψ j (t - a) (κ * x)))
        Tendsto wn atTop (𝓝 w) ∧ Tendsto (fun j => V (wn j)) atTop (𝓝 (V w)) ∧
        (∀ j, 1 / 2 ≤ m j ∧ m j ≤ 3 / 2) ∧ Tendsto m atTop (𝓝 1) ∧
        Continuous (Function.uncurry q) ∧
        Continuous (fun z : ℝ × ℝ => deriv (q z.1) z.2) ∧
        (∀ t, Function.Periodic (q t) L) ∧ (∀ x, q 0 x = c0 x) ∧
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x, q t x ∈ U ∧
          mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0) ∧
        (∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
          ‖qn j 0 x - c0 x‖ < eps ∧ ‖deriv (qn j 0) x - deriv c0 x‖ < eps ∧
            ‖deriv (deriv (qn j 0)) x - deriv (deriv c0) x‖ < eps) ∧
        ∀ j,
          ContDiffOn ℝ ∞ (Function.uncurry (qn j)) (Icc (0 : ℝ) T ×ˢ univ) ∧
          (∀ t : Icc (0 : ℝ) T, ContDiffAt ℝ ∞
            (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (V (wn j) t)) 0) ∧
          (∀ t, Function.Periodic (qn j t) L) ∧
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x, qn j t x ∈ U ∧
            mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (qn j t x) (deriv (qn j t) x) ≠ 0) ∧
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x, qn j t x = e (ρ (qn j t x))) ∧
          (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => qn j s x)
            (A j t x • deriv (deriv (qn j t)) x +
              ambientCurveLower F e ρ (a + t) (qn j t x) (deriv (qn j t) x)) t) ∧
          (∀ x, curveSpeed F (fun y _ => ρ (qn j 0 y)) a x = m j) ∧
          (∀ x, ψ j 0 x = x) ∧
          (∀ t ∈ Icc (0 : ℝ) S, ∀ x, ψ j t (x + L) = ψ j t x + L) ∧
          ContDiffOn ℝ ∞ (Function.uncurry (ψ j)) (Icc (0 : ℝ) S ×ˢ univ) ∧
          (∀ t ∈ Icc (0 : ℝ) S, ∀ x, HasDerivWithinAt (fun s => ψ j s x)
            (deriv (A j t) (ψ j t x) / 2) (Icc (0 : ℝ) S) t) ∧
          (∀ t ∈ Icc (0 : ℝ) S, ∀ x, 0 < deriv (ψ j t) x) ∧
          (∀ t ∈ Icc (0 : ℝ) S, Function.Bijective (ψ j t)) ∧
          M63SmoothShrinkingCurveOn F (cn j) (Icc a (a + S)) ∧
          (∀ x, cn j x a = ρ (qn j 0 (κ * x))) ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
            (fun z : ℝ × ℝ => cn j z.1 z.2) (univ ×ˢ Icc a (a + S)) := by
  classical
  dsimp only
  have hab : a < b := by linarith only [hTcap, hTcapb]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨r, m0, w, zn, hm0, hm0lim, _hr, _hrp, hrfix, _hrimm,
      hrspeed, hrnear, hw, hzn, hznlim, hphase⟩ :=
    exists_smooth_fixedPeriod_spectral_approximants F he hU heU hρ hρe ha hγp hγ himm hunit
  let c0 := fun x => e (γ x)
  have hc0 : ContDiff ℝ 2 c0 :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hγ).contDiff
  have hproject (x : ℝ) : mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c0 x) (deriv c0 x) =
      curveVelocity (n := n) γ x := by
    have hv : curveVelocity (n := n) (fun y => ρ (c0 y)) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (c0 x) (deriv c0 x) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ c0) x) 1 = _
      erw [mfderiv_comp x
        ((hρ.contMDiffAt (hU.mem_nhds (heU (mem_range_self _)))).mdifferentiableAt (by simp))
        ((hc0.contMDiff x).mdifferentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
      rfl
    have hid : (fun y => ρ (c0 y)) = γ := funext fun y => hρe (γ y)
    rw [hid] at hv
    exact hv.symm
  have hprincipal (x : ℝ) : ambientCurvePrincipal F ρ a (c0 x) (deriv c0 x) = 1 := by
    unfold ambientCurvePrincipal
    rw [hproject]
    change ((F.metric a).inner (ρ (e (γ x))) (curveVelocity γ x) (curveVelocity γ x))⁻¹ = 1
    rw [hρe, ← M62.speed_sq F (fun y _ => γ y) a x, hunit]
    norm_num
  let E : (ι → ℝ) ≃L[ℝ] W := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let jet := fun (z : StateV) (x : AddCircle L) =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  have hwjet (x : ℝ) : jet w (x : AddCircle L) = (c0 x, deriv c0 x) :=
    Prod.ext (hw x).1 (hw x).2
  let K := range (jet w)
  have hK : IsCompact K := isCompact_range
    ((E.continuous.comp (vectorPeriodicJet (L := L) 1 0 (by omega) w).continuous).prodMk
      (E.continuous.comp (vectorPeriodicJet (L := L) 1 1 (by omega) w).continuous))
  have hKsub : K ⊆ {z : W × W |
      z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} := by
    rintro z ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change (jet w (y : AddCircle L)).1 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet w (y : AddCircle L)).1
        (jet w (y : AddCircle L)).2 ≠ 0
    rw [hwjet]
    exact ⟨heU (mem_range_self _), by rw [hproject]; exact himm y⟩
  have hunitjet (x : AddCircle L) :
      ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hwjet]
    exact hprincipal y
  obtain ⟨T, hT, hTTcap, hT1, B, u, hB, hwB, hpath,
      _hqc, hqxc, hperiod, hzero, hguard, hflow⟩ :=
    exists_common_ambient_spectral_family F he hU heU hρ hρe hK hKsub w hTcap hTcapb
      (fun x => mem_range_self x) hunitjet
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hznlim.eventually (hB.mem_nhds hwB))
  let wn := fun j => zn (N0 + j)
  let m := fun j => m0 (N0 + j)
  have hshift : Tendsto (fun j : ℕ => N0 + j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat N0
  have hwnlim : Tendsto wn atTop (𝓝 w) := hznlim.comp hshift
  have hwnB (j : ℕ) : wn j ∈ B := hN0 (N0 + j) (Nat.le_add_right N0 j)
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := fun z : StateV => initialResponseTrace lambda z hT.le (u z)
  let Q := fun z : StateV => initialResponseCurve (L := L) hT.le z (u z)
  have hVlim : Tendsto (fun j => V (wn j)) atTop (𝓝 (V w)) :=
    (hpath.continuousOn.continuousAt (hB.mem_nhds hwB)).tendsto.comp hwnlim
  have hQxc : Continuous (fun z : ℝ × ℝ => deriv (Q w z.1) z.2) := by
    exact ContinuousOn.comp_continuous
      (g := fun z : StateV × (ℝ × ℝ) => deriv (Q z.1 z.2.1) z.2.2)
      (f := fun z : ℝ × ℝ => (w, z)) (s := B ×ˢ (univ : Set (ℝ × ℝ)))
      hqxc (continuous_const.prodMk continuous_id) (fun _ => ⟨hwB, mem_univ _⟩)
  have hQzero (j : ℕ) : Q (wn j) 0 = r (N0 + j) :=
    funext fun x => (hzero (wn j) (hwnB j) x).trans (hzn (N0 + j) x).1
  have hflowj (j : ℕ) := hflow (wn j) (hwnB j) (hphase (N0 + j)).contDiffAt
  have hfixed (j : ℕ) : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      Q (wn j) t x = e (ρ (Q (wn j) t x)) := by
    apply (hflowj j).2.2.2
    intro x
    change Q (wn j) 0 x = e (ρ (Q (wn j) 0 x))
    rw [hQzero]
    exact (hrfix (N0 + j) x).2.symm
  have htime (j : ℕ) : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      HasDerivAt (fun s => Q (wn j) s x)
        (ambientCurvePrincipal F ρ (a + t) (Q (wn j) t x) (deriv (Q (wn j) t) x) •
            deriv (deriv (Q (wn j) t)) x +
          ambientCurveLower F e ρ (a + t) (Q (wn j) t x) (deriv (Q (wn j) t) x)) t := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (hflowj j).2.2.1
  have hTb : a + T ≤ b := by linarith only [hTTcap, hTcapb]
  have hS : 0 < T / 4 := by positivity
  have hS1 : T / 4 ≤ 1 / 2 := by linarith only [hT1]
  have hlabels (j : ℕ) := exists_normal_curve_on_prescribed_ambient_slab
    F he hU heU hρ hρe (Fact.out : 0 < L) hT hS hTb le_rfl hS1
      (hflowj j).1 (fun t _ => hperiod (wn j) (hwnB j) t)
      (hguard (wn j) (hwnB j)) (hfixed j) (htime j)
  choose ψ hψ using hlabels
  refine ⟨T, hT, hTTcap, hT1, w, wn, m, u, ψ, hwnlim, hVlim,
    fun j => hm0 (N0 + j), hm0lim.comp hshift,
    (initialResponseCurve_spec (L := L) hT.le w (u w)).1, hQxc,
    hperiod w hwB, fun x => (hzero w hwB x).trans (hw x).1,
    hguard w hwB, ?_, ?_⟩
  · intro eps heps
    obtain ⟨N, hN⟩ := hrnear eps heps
    refine ⟨N, fun j hj x => ?_⟩
    change ‖Q (wn j) 0 x - c0 x‖ < eps ∧
      ‖deriv (Q (wn j) 0) x - deriv c0 x‖ < eps ∧
      ‖deriv (deriv (Q (wn j) 0)) x - deriv (deriv c0) x‖ < eps
    rw [hQzero]
    exact hN (N0 + j) (hj.trans (Nat.le_add_left j N0)) x
  · intro j
    refine ⟨(hflowj j).1, (hflowj j).2.1, hperiod (wn j) (hwnB j),
      hguard (wn j) (hwnB j), hfixed j, htime j, ?_, hψ j⟩
    intro x
    change curveSpeed F (fun y _ => ρ (Q (wn j) 0 y)) a x = m j
    rw [hQzero]
    exact hrspeed (N0 + j) x

end PoincareConjecture.M63
