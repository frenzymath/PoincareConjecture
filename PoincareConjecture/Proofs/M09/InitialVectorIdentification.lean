import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.VelocityRestriction
import PoincareConjecture.Proofs.M09.CurvePhase

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_eq_of_eqOn {γ δ : ℝ → M} {I : Set ℝ} {s : ℝ}
    (heq : Set.EqOn γ δ I) (hs : s ∈ I) (hI : UniqueDiffWithinAt ℝ I s)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (hδ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) δ s) :
    (curveVelocity (n := n) γ s : V) = curveVelocity (n := n) δ s := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
    (fun r hr ↦ heq hr) hs
  rw [mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt hγ,
    mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt hδ] at hd
  exact congrArg (fun L : ℝ →L[ℝ] V ↦ L 1) hd

variable {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem lExponentialFamily_regularization_eqOn (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    Set.EqOn (A.regularization Z b hb hmax).path.curve (A.squareFamily Z)
      (sqrtParameterInterval 0 b) := by
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  have hsmax : s < Real.sqrt τmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
  exact ((A.regularization Z b hb hmax).path.agrees s hs).trans
    ((congrFun (A.path_eq Z b hb hmax) (s ^ 2)).trans
      (A.square_agrees Z s ⟨hs0, hsmax⟩).symm)

theorem lExponentialFamily_initial_velocity (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) :
    (curveVelocity (n := n) (A.squareFamily Z) 0 : V) = (2 : ℝ) • Z := by
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  have hi := A.initial_derivative Z
  rw [hcast] at hi
  exact hi

theorem lExponentialFamily_regularization_initial_phase (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    curvePhase (n := n) (A.regularization Z b hb hmax).path.curve 0 =
      Bundle.TotalSpace.mk' V p ((2 : ℝ) • Z) := by
  let R := A.regularization Z b hb hmax
  let K := sqrtParameterInterval 0 b
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hzero : (0 : ℝ) ∈ K := by rw [hK]; exact ⟨le_rfl, Real.sqrt_nonneg b⟩
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have heq := lExponentialFamily_regularization_eqOn A Z b hb hmax
  have hx : R.path.curve 0 = p := (heq hzero).trans (A.square_at_zero Z)
  have hR : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) R.path.curve 0 :=
    (R.path.smooth.contMDiffAt
      (R.path.open_domain.mem_nhds (R.path.interval_subset hzero))).mdifferentiableAt (by simp)
  have hA := (lExponentialFamily_squareSlice_contMDiffAt A Z 0
    ⟨le_rfl, Real.sqrt_pos.mpr (hb.trans hmax)⟩).mdifferentiableAt (by simp)
  have hv := curveVelocity_eq_of_eqOn heq hzero (hKdiff 0 hzero) hR hA
  exact Bundle.TotalSpace.ext hx (heq_of_eq (hv.trans (lExponentialFamily_initial_velocity A Z)))

theorem lExponentialFamily_initialVector_eq_of_eqOn (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (heq : Set.EqOn (A.gamma Z) (A.gamma W) (Set.Icc 0 b)) : Z = W := by
  let K := Set.Icc 0 (Real.sqrt b)
  have hroot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hrootmax : Real.sqrt b < Real.sqrt τmax := Real.sqrt_lt_sqrt hb.le hmax
  have hzero : (0 : ℝ) ∈ K := ⟨le_rfl, hroot.le⟩
  have hsqeq : Set.EqOn (A.squareFamily Z) (A.squareFamily W) K := by
    intro s hs
    have hsmax : s < Real.sqrt τmax := hs.2.trans_lt hrootmax
    have hsq : s ^ 2 ∈ Set.Icc 0 b := by
      refine ⟨sq_nonneg s, ?_⟩
      nlinarith [hs.1, hs.2, Real.sq_sqrt hb.le]
    exact (A.square_agrees Z s ⟨hs.1, hsmax⟩).trans
      ((heq hsq).trans (A.square_agrees W s ⟨hs.1, hsmax⟩).symm)
  have hd (Y : TangentSpace (𝓡 n) p) :=
    (lExponentialFamily_squareSlice_contMDiffAt A Y 0
      ⟨le_rfl, Real.sqrt_pos.mpr (hb.trans hmax)⟩).mdifferentiableAt (by simp)
  have hv := curveVelocity_eq_of_eqOn hsqeq hzero
    (uniqueDiffOn_Icc hroot 0 hzero) (hd Z) (hd W)
  have htwo : (2 : ℝ) • Z = (2 : ℝ) • W :=
    (lExponentialFamily_initial_velocity A Z).symm.trans
      (hv.trans (lExponentialFamily_initial_velocity A W))
  exact (smul_right_injective (M := TangentSpace (𝓡 n) p) (by norm_num : (2 : ℝ) ≠ 0)) htwo

end PoincareConjecture.Proofs.M09
