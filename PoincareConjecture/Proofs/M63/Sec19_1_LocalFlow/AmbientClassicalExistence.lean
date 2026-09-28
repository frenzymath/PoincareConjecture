import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurvePreservation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientSmoothResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothSpectralInitialOrbit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothSpectralTraceOrbit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralResponseClassical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_ambient_classical_curve_of_unit_initial
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {L : ℝ} (hL : 0 < L) (f : C(AddCircle L, W))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L)))
    (hguard : ∀ x : ℝ, f (x : AddCircle L) ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f (x : AddCircle L))
        (deriv (fun y : ℝ => f (y : AddCircle L)) x) ≠ 0)
    (hunit : ∀ x : ℝ, ambientCurvePrincipal F ρ a (f (x : AddCircle L))
      (deriv (fun y : ℝ => f (y : AddCircle L)) x) = 1)
    (hfixed : ∀ x : ℝ, f (x : AddCircle L) = e (ρ (f (x : AddCircle L))))
    {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a) :
    ∃ T : ℝ, 0 < T ∧ T ≤ Tcap ∧ T ≤ 1 ∧ ∃ q : ℝ → ℝ → W,
      Continuous (Function.uncurry q) ∧
      (∀ t, Function.Periodic (q t) L) ∧
      (∀ x : ℝ, q 0 x = f (x : AddCircle L)) ∧
      (∀ t, ContDiff ℝ ∞ (q t)) ∧
      (∀ k : ℕ, ∃ J : C(Icc (0 : ℝ) T, C(AddCircle L, W)),
        ∀ (t : Icc (0 : ℝ) T) (x : ℝ),
          iteratedDeriv k (q (t : ℝ)) x = J t (x : AddCircle L)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => q s x)
        (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
            iteratedDeriv 2 (q t) x +
          ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t) ∧
      ContDiffOn ℝ 1 (Function.uncurry q) (Ioo (0 : ℝ) T ×ˢ univ) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, q t x = e (ρ (q t x)) := by
  let : Fact (0 < L) := ⟨hL⟩
  let E : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let f' : C(AddCircle L, ι → ℝ) :=
    E.symm.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L) f
  have hf' : ContDiff ℝ ∞ (fun x : ℝ => f' (x : AddCircle L)) :=
    E.symm.contDiff.comp hf
  obtain ⟨w, _hcoeff, hrec, _hbase, hw⟩ :=
    exists_smooth_vectorPeriodic_spectral_initial_state f' hf'
  let jet : S → AddCircle L → W × W := fun v x =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) v x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) v x))
  have hzero (x : AddCircle L) : (jet w x).1 = f x := by
    change E (vectorPeriodicJet (L := L) 1 0 (by omega) w x) = f x
    rw [hrec]
    exact E.apply_symm_apply (f x)
  have hfirst (x : ℝ) : (jet w (x : AddCircle L)).2 =
      deriv (fun y : ℝ => f (y : AddCircle L)) x := by
    have heq : (fun y : ℝ => E
        (vectorPeriodicJet (L := L) 1 0 (by omega) w (y : AddCircle L))) =
        (fun y : ℝ => f (y : AddCircle L)) := funext fun y => hzero (y : AddCircle L)
    have hd := E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (k := 1) (j := 0) (by omega) w x)
    change HasDerivAt (fun y : ℝ => E
      (vectorPeriodicJet (L := L) 1 0 (by omega) w (y : AddCircle L)))
      ((jet w (x : AddCircle L)).2) x at hd
    rw [heq] at hd
    exact hd.deriv.symm
  let K := range (jet w)
  have hjetc : Continuous (jet w) :=
    (E.continuous.comp (vectorPeriodicJet (L := L) 1 0 (by omega) w).continuous).prodMk
      (E.continuous.comp (vectorPeriodicJet (L := L) 1 1 (by omega) w).continuous)
  have hK : IsCompact K := isCompact_range hjetc
  have hKsub : K ⊆ {z : W × W |
      z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} := by
    rintro z ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change (jet w (y : AddCircle L)).1 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet w (y : AddCircle L)).1
        (jet w (y : AddCircle L)).2 ≠ 0
    rw [hzero, hfirst]
    exact hguard y
  have hunitjet (x : AddCircle L) :
      ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hzero, hfirst]
    exact hunit y
  obtain ⟨T, hT, hTTcap, hT1, F0, u, _huw, _hu, htrace, hbranch, hinside, hsource⟩ :=
    exists_ambient_smooth_response (L := L) F he hU hρ hK hKsub w hTcap hTcapb
      (fun x => mem_range_self x) hunitjet
  have hTb : a + T ≤ b := by linarith
  have horbit := contDiffAt_initialResponseTrace_spectral_orbit (L := L)
    hT.le w F0 u htrace hw.contDiffAt hbranch
  let q := initialResponseCurve (L := L) hT.le w F0
  obtain ⟨hqc, hper, hqzero, hqd⟩ := initialResponseCurve_spec (L := L) hT.le w F0
  obtain ⟨hspace, hjets⟩ :=
    initialResponseCurve_spatial_jets (L := L) hT.le w F0 horbit
  obtain ⟨htime, hC1⟩ :=
    initialResponseCurve_classical F he hU hρ hT.le hTb w F0 horbit hinside hsource
  have hqinitial (x : ℝ) : q 0 x = f (x : AddCircle L) :=
    (hqzero x).trans (hzero (x : AddCircle L))
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := initialResponseTrace lambda w hT.le F0
  have hqguard (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℝ) :
      q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0 := by
    have hqvalue : q t x = (jet (V ⟨t, ht⟩) (x : AddCircle L)).1 := by
      dsimp only [q, initialResponseCurve]
      rw [projIcc_of_mem hT.le ht]
      rfl
    have hqderiv : deriv (q t) x = (jet (V ⟨t, ht⟩) (x : AddCircle L)).2 := by
      have hd := (hqd t x).deriv
      rw [projIcc_of_mem hT.le ht] at hd
      exact hd
    rw [hqvalue, hqderiv]
    exact hinside ⟨t, ht⟩ (x : AddCircle L)
  have hqxc : ContinuousOn (fun z : ℝ × ℝ => deriv (q z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
    have heq : (fun z : ℝ × ℝ => deriv (q z.1) z.2) =
        (fun z : ℝ × ℝ => E (vectorPeriodicJet (L := L) 1 1 (by omega)
          (V (projIcc 0 T hT.le z.1)) (z.2 : AddCircle L))) :=
      funext fun z => (hqd z.1 z.2).deriv
    rw [heq]
    exact (E.continuous.comp (continuous_eval.comp
      (((vectorPeriodicJet (L := L) (ι := ι) 1 1 (by omega)).continuous.comp
        (V.continuous.comp (continuous_projIcc.comp continuous_fst))).prodMk
          ((AddCircle.continuous_mk' L).comp continuous_snd)))).continuousOn
  have hpres := ambientCurve_preserves_retraction F he hU heU hρ hρe hL hT hTb q
    hqc.continuousOn hqxc (fun t _ => hper t)
    (fun t _ => (hspace t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hqguard htime (fun x => by rw [hqinitial]; exact hfixed x)
  exact ⟨T, hT, hTTcap, hT1, q, hqc, hper, hqinitial, hspace, hjets,
    hqguard, htime, hC1, hpres⟩

end PoincareConjecture.M63
