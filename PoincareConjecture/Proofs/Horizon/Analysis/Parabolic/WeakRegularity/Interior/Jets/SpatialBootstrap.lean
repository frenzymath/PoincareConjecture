




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.LocalForcedSecondJets
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJetAlgebra
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakDifferentiatedEquation










open Set MeasureTheory Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

private theorem weak_identity_restrict {n : ℕ} {U V : Set (Spacetime n)}
    (hVU : V ⊆ U) {u g : Spacetime n → ℝ} (v : Spacetime n)
    (hw : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y in U, φ y * g y) = -(∫ y in U, fderiv ℝ φ y v * u y))
    (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ y in V, φ y * g y) = -(∫ y in V, fderiv ℝ φ y v * u y) := by
  have hpair {ψ : Spacetime n → ℝ} (hψ : tsupport ψ ⊆ V) (a : Spacetime n → ℝ) :
      (∫ y in V, ψ y * a y) = ∫ y in U, ψ y * a y := by
    calc
      _ = ∫ y, ψ y * a y := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h)), zero_mul])
      _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hVU (hψ h))), zero_mul])).symm
  rw [hpair hφV, hpair (ψ := fun y => fderiv ℝ φ y v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφV)]
  exact hw φ hφ hφc (hφV.trans hVU)

private theorem finite_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ f i := by
  classical
  have aux (s : Finset ι) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨d, hd, hdf⟩ := ih
      refine ⟨min (f i) d, lt_min (hf i) hd, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hdf j hj)
  simpa using aux Finset.univ

theorem exists_local_forced_spatial_jet
    {n k : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (hf : HasSpatialL2Jet U k f)
    {g : Fin n → Spacetime n → ℝ}
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict U))
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    (hweak : ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y))
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      HasSpatialL2Jet (ball z r) (k + 2) u ∧
      ∀ i, HasSpatialL2Jet (ball z r) (k + 1) (g i) := by
  classical
  induction k generalizing U u f g with
  | zero =>
    obtain ⟨r, hr, hrU, T, H, hT, hH, hgw, hTw, hHw⟩ :=
      exists_local_forced_weak_second_jets_of_memLpOn hU hC hprincipalc hdriftc hzerothc
        hu hf hg hforce hweak hz hκ hEll
    have hbU : ball z r ⊆ U := ball_subset_closedBall.trans hrU
    have hgj (j : Fin n) : HasSpatialL2Jet (ball z r) 1 (g j) :=
      ⟨(hg j).mono_measure (Measure.restrict_mono hbU le_rfl),
        fun i => H i j, fun i => (hH i j).restrict _, fun i => hHw i j⟩
    exact ⟨r, hr, hrU,
      ⟨hu.mono_measure (Measure.restrict_mono hbU le_rfl), g, hgj, hgw⟩, hgj⟩
  | succ k ih =>
    obtain ⟨R, hR, hRU, huR, hgR⟩ := ih hU hu hf.lower hg hforce hweak hz
    have hbU : ball z R ⊆ U := ball_subset_closedBall.trans hRU
    have hweakR (i : Fin n) (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
        (hφc : HasCompactSupport φ) (hφR : tsupport φ ⊆ ball z R) :
        (∫ y in ball z R, φ y * g i y) = -(∫ y in ball z R, spatialDeriv i φ y * u y) :=
      weak_identity_restrict hbU (spatialDirection i) (hweak i) φ hφ hφc hφR
    obtain ⟨hfm, fv, hfv, hfvweak⟩ := hf.restrict hbU
    choose A hA hAw using fun j => (hgR j).2
    let H (i j : Fin n) := A j i
    have hHJ (i j : Fin n) : HasSpatialL2Jet (ball z R) k (H i j) := hA j i
    have hHW (i j : Fin n) (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
        (hφc : HasCompactSupport φ) (hφR : tsupport φ ⊆ ball z R) :
        (∫ y in ball z R, φ y * H i j y) =
          -(∫ y in ball z R, spatialDeriv i φ y * g j y) := hAw j i φ hφ hφc hφR
    let F (j : Fin n) (y : Spacetime n) := fv j y +
      (∑ a, ∑ b, spatialDeriv j (C.principal a b) y * H a b y) -
      (∑ a, spatialDeriv j (C.drift a) y * g a y) - spatialDeriv j C.zeroth y * u y
    have hFJ (j : Fin n) : HasSpatialL2Jet (ball z R) k (F j) := by
      have hprincipal (a b : Fin n) : HasSpatialL2Jet (ball z R) k
          (fun y => spatialDeriv j (C.principal a b) y * H a b y) :=
        (hHJ a b).mul_smooth isOpen_ball
          (contDiff_spatialDeriv (contDiffOn_univ.mp (hC.1 a b)) j)
          ((hprincipalc a b).fderiv_apply ℝ _)
      have hdrift (a : Fin n) : HasSpatialL2Jet (ball z R) k
          (fun y => spatialDeriv j (C.drift a) y * g a y) :=
        (hgR a).lower.mul_smooth isOpen_ball
          (contDiff_spatialDeriv (contDiffOn_univ.mp (hC.2.1 a)) j)
          ((hdriftc a).fderiv_apply ℝ _)
      have hzero : HasSpatialL2Jet (ball z R) k
          (fun y => spatialDeriv j C.zeroth y * u y) :=
        (huR.of_le (by omega : k ≤ k + 2)).mul_smooth isOpen_ball
          (contDiff_spatialDeriv (contDiffOn_univ.mp hC.2.2) j)
          (hzerothc.fderiv_apply ℝ _)
      exact ((hfv j).add (HasSpatialL2Jet.sum Finset.univ
        (fun a _ => HasSpatialL2Jet.sum Finset.univ (fun b _ => hprincipal a b)))).sub
          (HasSpatialL2Jet.sum Finset.univ (fun a _ => hdrift a)) |>.sub hzero
    have hCR : C.IsSmoothOn (ball z R) :=
      ⟨fun i j => (hC.1 i j).mono (subset_univ _),
        fun i => (hC.2.1 i).mono (subset_univ _), hC.2.2.mono (subset_univ _)⟩
    have hforceR (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
        (hφc : HasCompactSupport φ) (hφR : tsupport φ ⊆ ball z R) :
        (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y :=
      hforce φ hφ hφc (hφR.trans hbU)
    have hforceJ (j : Fin n) (φ : Spacetime n → ℝ) (hφ : ContDiff ℝ ∞ φ)
        (hφc : HasCompactSupport φ) (hφR : tsupport φ ⊆ ball z R) :
        (∫ y, g j y * C.adjoint φ y) = ∫ y, φ y * F j y :=
      differentiated_inhomogeneous_pairing isOpen_ball hCR huR.locallyIntegrableOn
        ((hf.restrict hbU).locallyIntegrableOn) (hfv j).locallyIntegrableOn hforceR
        (spatialDirection j) (fun i => (hgR i).locallyIntegrableOn)
        (fun i j => (hHJ i j).locallyIntegrableOn) (hgR j).locallyIntegrableOn
        hweakR hHW (hweakR j) (hfvweak j) hφ hφc hφR
    have hnext (j : Fin n) : ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ ball z R ∧
        HasSpatialL2Jet (ball z s) (k + 2) (g j) := by
      obtain ⟨s, hs, hsR, hgj, hHj⟩ := ih isOpen_ball (hgR j).memLp (hFJ j)
        (fun i => (hHJ i j).memLp) (hforceJ j) (fun i => hHW i j) (mem_ball_self hR)
      exact ⟨s, hs, hsR, hgj⟩
    choose S hS hSR hSJ using hnext
    obtain ⟨d, hd, hdS⟩ := finite_lower_bound S hS
    let s : ℝ := min (R / 2) d
    have hs : 0 < s := lt_min (by positivity) hd
    have hsR : closedBall z s ⊆ ball z R := by
      intro y hy
      exact (mem_closedBall.mp hy).trans_lt
        ((min_le_left (R / 2) d).trans_lt (by linarith))
    have hsU : ball z s ⊆ U := ball_subset_closedBall.trans (hsR.trans hbU)
    have hgS (j : Fin n) : HasSpatialL2Jet (ball z s) (k + 2) (g j) :=
      (hSJ j).restrict (ball_subset_ball ((min_le_right _ _).trans (hdS j)))
    refine ⟨s, hs, hsR.trans hbU, ?_, hgS⟩
    refine ⟨hu.mono_measure (Measure.restrict_mono hsU le_rfl), g, hgS, ?_⟩
    intro i φ hφ hφc hφs
    exact weak_identity_restrict hsU (spatialDirection i) (hweak i) φ hφ hφc hφs


end Poincare.Analysis.Parabolic.WeakRegularity.Interior
