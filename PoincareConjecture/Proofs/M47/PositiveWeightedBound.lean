import PoincareConjecture.Proofs.M47.PositivePinching
import PoincareConjecture.Proofs.M47.PositiveWeightedMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Coefficients
import PoincareConjecture.Proofs.M05.Analysis.Parabolic.CompactMaximum












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]





theorem exists_uniform_weighted_ricci_bound
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        ((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) /
          (F.connection t).scalarCurvature x ^ (2 - epsilon) ≤ C := by
  obtain ⟨delta, hdelta, _, hpinch⟩ := exists_uniform_ricci_pinching hC hT F hpos
  obtain ⟨r, hr, hlower⟩ := exists_uniform_positive_scalar_lower hT F hpos
  have hR (t : ℝ) (ht : t ∈ Ico 0 T) (x : M) :
      0 < (F.connection t).scalarCurvature x := hr.trans_le (hlower t ht x)
  let epsilon := min (delta ^ 2) (1 / 2 : ℝ)
  have hepsilon : 0 < epsilon := lt_min (sq_pos_of_pos hdelta) (by norm_num)
  have hepsilon1 : epsilon ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hepsilon2 : epsilon ≤ 2 * delta ^ 2 := by
    have h := min_le_left (delta ^ 2) (1 / 2 : ℝ)
    dsimp only [epsilon]
    nlinarith [sq_nonneg delta]
  let p := 2 - epsilon
  have hp : 1 ≤ p := by dsimp only [p]; linarith
  have hp' : p ≤ 2 := by dsimp only [p]; linarith
  let q := fun t x =>
    ((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) /
      (F.connection t).scalarCurvature x ^ p
  have hq0 : Continuous (q 0) :=
    (contMDiff_weighted_ricci_defect (F.connection 0)
      (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0))
      (hR 0 ⟨le_rfl, hT⟩) p).continuous
  obtain ⟨C0, hC0⟩ := isCompact_univ.bddAbove_image hq0.continuousOn
  let C := max 1 C0
  have hCpos : 0 < C := (by norm_num : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hinit (x : M) : q 0 x ≤ C :=
    (hC0 ⟨x, mem_univ x, rfl⟩).trans (le_max_right _ _)
  have hRjoint := (hC.scalar_regular 3 M (Ico 0 T) F).continuousOn
  have hSjoint := RicciFlowAnalysis.continuousOn_flow_ricciNormSq F
  have hqjoint : ContinuousOn (fun z : ℝ × M => q z.1 z.2) (Ico 0 T ×ˢ univ) := by
    exact (hSjoint.sub ((hRjoint.pow 2).div_const 3)).div
      (hRjoint.rpow_const (fun z hz => Or.inl (hR z.1 hz.1 z.2).ne'))
      (fun z hz => (Real.rpow_pos_of_pos (hR z.1 hz.1 z.2) p).ne')
  refine ⟨epsilon, C, hepsilon, hepsilon1, hCpos, ?_⟩
  intro t ht x
  let W := fun y s => q s y - C
  let W' := fun y s => deriv (fun a => q a y) s
  have htime (s : ℝ) (hs : s ∈ Icc 0 t) : s ∈ Ico 0 T :=
    ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hinterior (s : ℝ) (hs : s ∈ Ioc 0 t) : s ∈ interior (Ico 0 T) := by
    rw [interior_Ico]
    exact ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hW : ContinuousOn (Function.uncurry W) (univ ×ˢ Icc 0 t) := by
    exact (hqjoint.comp (continuous_snd.prodMk continuous_fst).continuousOn
      (fun z hz => ⟨htime z.2 hz.2, mem_univ z.1⟩)).sub continuousOn_const
  have hderiv : ∀ y s, s ∈ Ioc 0 t →
      HasDerivWithinAt (W y) (W' y s) (Icc 0 t) s := by
    intro y s hs
    have hd := differentiableAt_weighted_ricci_defect hC F (hinterior s hs) y
      (hR s (htime s ⟨hs.1.le, hs.2⟩) y) p
    exact (hd.hasDerivAt.sub_const C).hasDerivWithinAt
  have hmax : ∀ y s, s ∈ Ioc 0 t → 0 < W y s →
      (∀ z, W z s ≤ W y s) → W' y s ≤ 0 * W y s := by
    intro y s hs _ hbound
    have hs' := htime s ⟨hs.1.le, hs.2⟩
    have hD := hC.tensor_calculus 3 M (F.metric s) (F.connection s)
    obtain ⟨a, b, c, _, _, _, hscalar, hnorm, _⟩ :=
      exists_pinched_ricci_spectrum (F.connection s) hD y (hpinch s hs' y)
    have hdefect : 0 ≤ (F.connection s).ricciNormSq y -
        (F.connection s).scalarCurvature y ^ 2 / 3 := by
      rw [hscalar, hnorm]
      exact Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq_nonneg a b c
    have hreact := weighted_ricci_reaction_nonpos (F.connection s) hD y hdelta.le
      (hR s hs' y) (hpinch s hs' y) hepsilon2
    have hmaxq : IsLocalMax (q s) y := Filter.Eventually.of_forall (fun z => by
      have hz := hbound z
      dsimp only [W] at hz
      linarith only [hz])
    have h := weighted_ricci_deriv_nonpos_at_localMax hC F (hinterior s hs)
      (hR s hs') hp hp' hdefect (by
        dsimp only
        rwa [show 2 - p = epsilon by dsimp only [p]; ring]) hmaxq
    simpa only [zero_mul] using h
  have hcomp := Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max hW hderiv hmax
    (fun y => sub_nonpos.mpr (hinit y))
  exact sub_nonpos.mp (hcomp x t ⟨ht.1, le_rfl⟩)




theorem exists_uniform_normalized_ricci_bound
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < C ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        ((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) /
          (F.connection t).scalarCurvature x ^ 2 ≤
            C / (F.connection t).scalarCurvature x ^ epsilon := by
  obtain ⟨epsilon, C, hepsilon, hepsilon1, hCpos, hbound⟩ :=
    exists_uniform_weighted_ricci_bound hC hT F hpos
  obtain ⟨r, hr, hlower⟩ := exists_uniform_positive_scalar_lower hT F hpos
  refine ⟨epsilon, C, hepsilon, hepsilon1, hCpos, ?_⟩
  intro t ht x
  have hR := hr.trans_le (hlower t ht x)
  have hquot :
      ((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) /
          (F.connection t).scalarCurvature x ^ 2 =
        (((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) /
          (F.connection t).scalarCurvature x ^ (2 - epsilon)) /
            (F.connection t).scalarCurvature x ^ epsilon := by
    rw [div_div, ← Real.rpow_add hR, show (2 - epsilon) + epsilon = 2 by ring,
      Real.rpow_two]
  rw [hquot]
  exact div_le_div_of_nonneg_right (hbound t ht x) (Real.rpow_nonneg hR.le epsilon)

end PoincareConjecture.M47Positive
