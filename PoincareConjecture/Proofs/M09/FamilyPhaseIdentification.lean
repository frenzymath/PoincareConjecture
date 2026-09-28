import PoincareConjecture.Proofs.M09.InitialVectorIdentification
import PoincareConjecture.Proofs.M09.WithinGeometricUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

local notation "Q" => EuclideanSpace ℝ (Fin n)

theorem lExponentialFamily_initialVector_eq_of_squarePhase {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p) (Z W : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (c : ℝ) (hc : c ∈ Set.Icc 0 (Real.sqrt b))
    (hphase : curvePhase (n := n) (A.squareFamily Z) c = curvePhase (n := n) (A.squareFamily W) c) : Z = W := by
  let K := sqrtParameterInterval 0 b
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp only [K, sqrtParameterInterval, Real.sqrt_zero]
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have hKconn : IsPreconnected K := hK ▸ isPreconnected_Icc
  have htime : K ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro s hs
    rw [hK] at hs
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hRphase (Y : TangentSpace (𝓡 n) p) (s : ℝ) (hs : s ∈ K) :
      curvePhase (n := n) (A.regularization Y b hb hmax).path.curve s =
        curvePhase (n := n) (A.squareFamily Y) s := by
    let R := A.regularization Y b hb hmax
    have heq := lExponentialFamily_regularization_eqOn A Y b hb hmax
    have hdR := (R.path.smooth.contMDiffAt
      (R.path.open_domain.mem_nhds (R.path.interval_subset hs))).mdifferentiableAt (by simp)
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    have hdA := (lExponentialFamily_squareSlice_contMDiffAt A Y s
      ⟨hs0, hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩).mdifferentiableAt (by simp)
    have hv := curveVelocity_eq_of_eqOn heq hs (hKdiff s hs) hdR hdA
    exact Bundle.TotalSpace.ext (heq hs) (heq_of_eq hv)
  let RZ := A.regularization Z b hb hmax
  let RW := A.regularization W b hb hmax
  let U := RZ.path.domain ∩ RW.path.domain
  have hU : IsOpen U := RZ.path.open_domain.inter RW.path.open_domain
  have hKU : K ⊆ U := fun s hs ↦ ⟨RZ.path.interval_subset hs, RW.path.interval_subset hs⟩
  have hcK : c ∈ K := hK ▸ hc
  have hRinit : curvePhase (n := n) RZ.path.curve c = curvePhase (n := n) RW.path.curve c :=
    (hRphase Z c hcK).trans (hphase.trans (hRphase W c hcK).symm)
  have heq := regularizedCurve_phase_eqOn_preconnected F hM04 T τmax hτmax hwindow
    RZ.path.curve RW.path.curve U K hU hKU hKdiff hKconn htime
    (RZ.path.smooth.mono Set.inter_subset_left) (RW.path.smooth.mono Set.inter_subset_right)
    RZ.velocity_extension RW.velocity_extension RZ.equation RW.equation c hcK hRinit
  have h0K : (0 : ℝ) ∈ K := by rw [hK]; exact ⟨le_rfl, Real.sqrt_nonneg b⟩
  have h0 := heq h0K
  change curvePhase (n := n) (A.regularization Z b hb hmax).path.curve 0 =
    curvePhase (n := n) (A.regularization W b hb hmax).path.curve 0 at h0
  rw [lExponentialFamily_regularization_initial_phase A Z b hb hmax,
    lExponentialFamily_regularization_initial_phase A W b hb hmax] at h0
  have hv : (2 : ℝ) • Z = (2 : ℝ) • W :=
    congrArg (fun v : TangentBundle (𝓡 n) M ↦ (v.2 : Q)) h0
  exact (smul_right_injective (M := TangentSpace (𝓡 n) p) (by norm_num : (2 : ℝ) ≠ 0)) hv

end PoincareConjecture.Proofs.M09
