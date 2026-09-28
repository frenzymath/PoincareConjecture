import PoincareConjecture.Proofs.M47.PositiveGradientBarrier
import PoincareConjecture.Proofs.M47.PositiveGradientThresholds
import PoincareConjecture.Proofs.M47.PositiveWeightedBound

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

theorem exists_uniform_scalar_gradient_bound
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Ico 0 T, ∀ x : M,
      (F.metric t).inner x
        ((F.connection t).gradient (F.connection t).scalarCurvature x)
        ((F.connection t).gradient (F.connection t).scalarCurvature x) ≤
      eta * (F.connection t).scalarCurvature x ^ 3 + K := by
  obtain ⟨delta, hdelta, _, hpinch⟩ := exists_uniform_ricci_pinching hC hT F hpos
  obtain ⟨r, hr, hlower⟩ := exists_uniform_positive_scalar_lower hT F hpos
  obtain ⟨epsilon, C, hepsilon, _, _, hnormalized⟩ :=
    exists_uniform_normalized_ricci_bound hC hT F hpos
  have hR (t : ℝ) (ht : t ∈ Ico 0 T) (x : M) :
      0 < (F.connection t).scalarCurvature x := hr.trans_le (hlower t ht x)
  have hRic (t : ℝ) (ht : t ∈ Ico 0 T) (x : M)
      (v : TangentSpace (𝓡 3) x) (hv : (F.metric t).inner x v v = 1) :
      0 ≤ (F.connection t).ricci x v v :=
    (mul_nonneg hdelta.le (hR t ht x).le).trans (hpinch t ht x v hv)
  let beta := min (eta / 2) 1
  have hbeta : 0 < beta := lt_min (by positivity) (by norm_num)
  have hbeta1 : beta ≤ 1 := min_le_right _ _
  have hbetaeta : beta ≤ eta / 2 := min_le_left _ _
  obtain ⟨L, hL, hreaction⟩ := exists_gradient_reaction_upper (C := C) hepsilon hbeta
  let H := fun s y => (F.metric s).inner y
    ((F.connection s).gradient (F.connection s).scalarCurvature y)
    ((F.connection s).gradient (F.connection s).scalarCurvature y) /
      (F.connection s).scalarCurvature y +
    240 * ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3) -
      beta * (F.connection s).scalarCurvature y ^ 2
  have hH0 : Continuous (H 0) :=
    (contMDiff_scalar_gradient_barrier (F.connection 0)
      (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)) (hR 0 ⟨le_rfl, hT⟩) beta).continuous
  obtain ⟨C0, hC0⟩ := isCompact_univ.bddAbove_image hH0.continuousOn
  let Cinit := max 0 C0
  have hCinit : 0 ≤ Cinit := le_max_left _ _
  have hinit (x : M) : H 0 x ≤ Cinit :=
    (hC0 ⟨x, mem_univ x, rfl⟩).trans (le_max_right _ _)
  have hHjoint := continuousOn_scalar_gradient_barrier hC F hR beta
  have hHbound (t : ℝ) (ht : t ∈ Ico 0 T) (x : M) : H t x ≤ Cinit + L * T := by
    let W := fun y s => H s y - L * s - Cinit
    let W' := fun y s => deriv (fun a => H a y) s - L
    have htime (s : ℝ) (hs : s ∈ Icc 0 t) : s ∈ Ico 0 T :=
      ⟨hs.1, hs.2.trans_lt ht.2⟩
    have hinterior (s : ℝ) (hs : s ∈ Ioc 0 t) : s ∈ interior (Ico 0 T) := by
      rw [interior_Ico]
      exact ⟨hs.1, hs.2.trans_lt ht.2⟩
    have hW : ContinuousOn (Function.uncurry W) (univ ×ˢ Icc 0 t) := by
      exact ((hHjoint.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun z hz => ⟨htime z.2 hz.2, mem_univ z.1⟩)).sub
          (continuousOn_const.mul continuousOn_snd)).sub continuousOn_const
    have hderiv : ∀ y s, s ∈ Ioc 0 t →
        HasDerivWithinAt (W y) (W' y s) (Icc 0 t) s := by
      intro y s hs
      have hd := differentiableAt_scalar_gradient_barrier hC F (hinterior s hs) y
        (hR s (htime s ⟨hs.1.le, hs.2⟩) y) beta
      convert ((hd.hasDerivAt.sub ((hasDerivAt_id s).const_mul L)).sub_const Cinit).hasDerivWithinAt
        using 1 <;> first | rfl | simp only [W', H, mul_one]
    have hmax : ∀ y s, s ∈ Ioc 0 t → 0 < W y s →
        (∀ z, W z s ≤ W y s) → W' y s ≤ 0 * W y s := by
      intro y s hs _ hbound
      have hs' := htime s ⟨hs.1.le, hs.2⟩
      have hD := hC.tensor_calculus 3 M (F.metric s) (F.connection s)
      have hnorm := ricci_norm_bounds_of_nonneg (F.connection s) hD y (hRic s hs' y)
      have hmaxH : IsLocalMax (H s) y := Filter.Eventually.of_forall (fun z => by
        have hz := hbound z
        dsimp only [W] at hz
        linarith only [hz])
      have hspatial := contMDiff_scalar_gradient_barrier (F.connection s) hD (hR s hs') beta
      have hLap := (F.connection s).laplacian_nonpos_of_isLocalMax hspatial hmaxH
      have hPDE := scalar_gradient_barrier_evolution_le hC F (hinterior s hs)
        (hR s hs') y (hRic s hs' y) hbeta.le hbeta1
      have hdefupper : (F.connection s).ricciNormSq y -
          (F.connection s).scalarCurvature y ^ 2 / 3 ≤
            (F.connection s).scalarCurvature y ^ 2 := by
        nlinarith only [hnorm.2, sq_nonneg ((F.connection s).scalarCurvature y)]
      have hreact := hreaction ((F.connection s).scalarCurvature y)
        ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3)
        (hR s hs' y) hdefupper (hnormalized s hs' y)
      change deriv (fun a => H a y) s ≤ (F.connection s).laplacian (H s) y +
        960 * (F.connection s).scalarCurvature y *
          ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3) -
        (4 * beta / 3) * (F.connection s).scalarCurvature y ^ 3 at hPDE
      change deriv (fun a => H a y) s - L ≤ 0 * W y s
      nlinarith only [hPDE, hLap, hreact]
    have hcomp := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max hW hderiv hmax
      (fun y => by simpa only [W, mul_zero, sub_zero] using sub_nonpos.mpr (hinit y))
    have h := hcomp x t ⟨ht.1, le_rfl⟩
    have hLt := mul_le_mul_of_nonneg_left ht.2.le hL
    dsimp only [W] at h
    linarith only [h, hLt]
  let C1 := Cinit + L * T
  have hC1 : 0 ≤ C1 := add_nonneg hCinit (mul_nonneg hL hT.le)
  obtain ⟨K, hK, habsorb⟩ := exists_linear_cubic_absorption (by positivity : 0 < eta / 2) hC1
  refine ⟨K, hK, ?_⟩
  intro t ht x
  have hRx := hR t ht x
  have hD := hC.tensor_calculus 3 M (F.metric t) (F.connection t)
  have hnorm := ricci_norm_bounds_of_nonneg (F.connection t) hD x (hRic t ht x)
  have hbarrier := hHbound t ht x
  have hquot : (F.metric t).inner x
      ((F.connection t).gradient (F.connection t).scalarCurvature x)
      ((F.connection t).gradient (F.connection t).scalarCurvature x) /
        (F.connection t).scalarCurvature x ≤
          beta * (F.connection t).scalarCurvature x ^ 2 + C1 := by
    dsimp only [H] at hbarrier
    change _ ≤ C1 at hbarrier
    linarith only [hbarrier, hnorm.1]
  have henergy := (div_le_iff₀ hRx).mp hquot
  have hlinear := habsorb ((F.connection t).scalarCurvature x) hRx
  have hbetacubic := mul_le_mul_of_nonneg_right hbetaeta (pow_nonneg hRx.le 3)
  nlinarith only [henergy, hlinear, hbetacubic]

end PoincareConjecture.M47Positive
