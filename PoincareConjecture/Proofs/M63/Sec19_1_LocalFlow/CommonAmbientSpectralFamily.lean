import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.OpenAmbientSmoothResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClassicalExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientClosedSmoothness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_common_ambient_spectral_family (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (w : S) {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let jet := fun (z : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
    (∀ x, jet w x ∈ K) →
    (∀ x, ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1) →
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (B : Set S) (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T),
        IsOpen B ∧ w ∈ B ∧
        ContDiffOn ℝ ∞ (fun z => initialResponseTrace lambda z hT.le (u z)) B ∧
        let q := fun z => initialResponseCurve (L := L) hT.le z (u z)
        ContinuousOn (fun z : S × (ℝ × ℝ) => q z.1 z.2.1 z.2.2) (B ×ˢ univ) ∧
        ContinuousOn (fun z : S × (ℝ × ℝ) => deriv (q z.1 z.2.1) z.2.2) (B ×ˢ univ) ∧
        (∀ z ∈ B, ∀ t, Function.Periodic (q z t) L) ∧
        (∀ z ∈ B, ∀ x : ℝ, q z 0 x = (jet z (x : AddCircle L)).1) ∧
        (∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
          q z t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q z t x) (deriv (q z t) x) ≠ 0) ∧
        ∀ z ∈ B,
          ContDiffAt ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s z) 0 →
          ContDiffOn ℝ ∞ (Function.uncurry (q z)) (Icc (0 : ℝ) T ×ˢ univ) ∧
          (∀ t : Icc (0 : ℝ) T, ContDiffAt ℝ ∞
            (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s
              (initialResponseTrace lambda z hT.le (u z) t)) 0) ∧
          (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => q z s x)
            (ambientCurvePrincipal F ρ (a + t) (q z t x) (deriv (q z t) x) •
                iteratedDeriv 2 (q z t) x +
              ambientCurveLower F e ρ (a + t) (q z t x) (deriv (q z t) x)) t) ∧
          ((∀ x, q z 0 x = e (ρ (q z 0 x))) →
            ∀ t ∈ Icc (0 : ℝ) T, ∀ x, q z t x = e (ρ (q z t x))) := by
  dsimp only
  intro hjet hunit
  obtain ⟨T, hT, hTTcap, hT1, _F0, u, B, hB, hwB, _huw, _hu,
      hpath, hbranch, hinside, hsource⟩ :=
    exists_open_ambient_smooth_response (L := L) F he hU hρ hK hsub w hTcap hTcapb
      hjet hunit
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := fun z : S => initialResponseTrace lambda z hT.le (u z)
  let q := fun z : S => initialResponseCurve (L := L) hT.le z (u z)
  let E : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hspec (z : S) := initialResponseCurve_spec (L := L) hT.le z (u z)
  have hVc : ContinuousOn (fun z : S × (ℝ × ℝ) =>
      V z.1 (projIcc 0 T hT.le z.2.1)) (B ×ˢ univ) := by
    have harg : ContinuousOn (fun z : S × (ℝ × ℝ) =>
        (V z.1, projIcc 0 T hT.le z.2.1)) (B ×ˢ univ) := by
      refine (hpath.continuousOn.comp continuousOn_fst (fun _ hz => hz.1)).prodMk ?_
      exact (continuous_projIcc.comp (continuous_fst.comp continuous_snd)).continuousOn
    exact continuous_eval.comp_continuousOn harg
  have hjetc (j : ℕ) (hj : j ≤ 1) : ContinuousOn
      (fun z : S × (ℝ × ℝ) => E (vectorPeriodicJet (L := L) 1 j hj
        (V z.1 (projIcc 0 T hT.le z.2.1)) (z.2.2 : AddCircle L))) (B ×ˢ univ) := by
    apply E.continuous.comp_continuousOn
    have harg : ContinuousOn (fun z : S × (ℝ × ℝ) =>
        (vectorPeriodicJet (L := L) 1 j hj (V z.1 (projIcc 0 T hT.le z.2.1)),
          (z.2.2 : AddCircle L))) (B ×ˢ univ) := by
      refine ((vectorPeriodicJet (L := L) (ι := ι) 1 j hj).continuous.comp_continuousOn
        hVc).prodMk ?_
      exact ((AddCircle.continuous_mk' L).comp
        (continuous_snd.comp continuous_snd)).continuousOn
    exact continuous_eval.comp_continuousOn harg
  have hguard (z : S) (hz : z ∈ B) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℝ) :
      q z t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q z t x) (deriv (q z t) x) ≠ 0 := by
    have hqvalue : q z t x = E
        (vectorPeriodicJet (L := L) 1 0 (by omega) (V z ⟨t, ht⟩) (x : AddCircle L)) := by
      dsimp only [q, initialResponseCurve]
      rw [projIcc_of_mem hT.le ht]
      rfl
    have hqderiv : deriv (q z t) x = E
        (vectorPeriodicJet (L := L) 1 1 (by omega) (V z ⟨t, ht⟩) (x : AddCircle L)) := by
      have hd := ((hspec z).2.2.2 t x).deriv
      rw [projIcc_of_mem hT.le ht] at hd
      exact hd
    rw [hqvalue, hqderiv]
    exact hinside z hz ⟨t, ht⟩ (x : AddCircle L)
  refine ⟨T, hT, hTTcap, hT1, B, u, hB, hwB, hpath, hjetc 0 (by omega),
    ?_, fun z _ => (hspec z).2.1, fun z _ => (hspec z).2.2.1, hguard, ?_⟩
  · apply (hjetc 1 (by omega)).congr
    intro z _
    exact ((hspec z.1).2.2.2 z.2.1 z.2.2).deriv
  · intro z hz hphase
    have hTb : a + T < b := by linarith
    have horbit := contDiffAt_initialResponseTrace_spectral_orbit (L := L)
      hT.le z (u z) u (hpath.contDiffAt (hB.mem_nhds hz)) hphase (hbranch z hz)
    have hstate (t : Icc (0 : ℝ) T) : ContDiffAt ℝ ∞
        (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (V z t)) 0 := by
      have heval := ((ContinuousMap.evalCLM ℝ t :
        C(Icc (0 : ℝ) T, S) →L[ℝ] S).contDiff.contDiffAt).comp 0 horbit
      have heq : (fun s : ℝ => initialResponseTrace lambda
          (vectorPeriodicSpectralTranslation (L := L) s z) hT.le
          ((vectorPeriodicSpectralTranslation (L := L) s).compLpL
            2 (timeMeasure T) (u z)) t) =
          fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (V z t) := by
        funext s
        exact vectorPeriodicSpectralTranslation_initialResponseTrace (L := L) hT.le z (u z) s t
      change ContDiffAt ℝ ∞ (fun s : ℝ => initialResponseTrace lambda
        (vectorPeriodicSpectralTranslation (L := L) s z) hT.le
        ((vectorPeriodicSpectralTranslation (L := L) s).compLpL
          2 (timeMeasure T) (u z)) t) 0 at heval
      rw [heq] at heval
      exact heval
    obtain ⟨hspace, hjets⟩ :=
      initialResponseCurve_spatial_jets (L := L) hT.le z (u z) horbit
    obtain ⟨htime, _hC1⟩ :=
      initialResponseCurve_classical F he hU hρ hT.le hTb.le z (u z) horbit
        (hinside z hz) (hsource z hz)
    have hjoint (k : ℕ) : ContinuousOn
        (fun p : ℝ × ℝ => iteratedDeriv k (q z p.1) p.2) (Icc 0 T ×ˢ univ) := by
      obtain ⟨J, hJ⟩ := hjets k
      have hcont : Continuous (fun p : ℝ × ℝ =>
          J (projIcc 0 T hT.le p.1) (p.2 : AddCircle L)) :=
        continuous_eval.comp ((J.continuous.comp
          (continuous_projIcc.comp continuous_fst)).prodMk
            ((AddCircle.continuous_mk' L).comp continuous_snd))
      apply hcont.continuousOn.congr
      intro p hp
      change iteratedDeriv k (q z p.1) p.2 = J (projIcc 0 T hT.le p.1) (p.2 : AddCircle L)
      rw [projIcc_of_mem hT.le hp.1]
      exact hJ ⟨p.1, hp.1⟩ p.2
    have hsmooth := ambientCurve_contDiffOn_infty_Icc F he hU hρ
      (Fact.out : 0 < L) hT hTb (fun t _ => (hspec z).2.1 t)
      (fun t _ => hspace t) hjoint (hguard z hz) htime
    refine ⟨hsmooth, hstate, htime, ?_⟩
    intro hfixed
    have hqxc : ContinuousOn (fun p : ℝ × ℝ => deriv (q z p.1) p.2)
        (Icc 0 T ×ˢ univ) := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hjoint 1
    exact ambientCurve_preserves_retraction F he hU heU hρ hρe
      (Fact.out : 0 < L) hT hTb.le (q z) (hspec z).1.continuousOn hqxc
      (fun t _ => (hspec z).2.1 t)
      (fun t _ => (hspace t).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hguard z hz) htime hfixed

end PoincareConjecture.M63
