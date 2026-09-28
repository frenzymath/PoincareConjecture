import PoincareConjecture.Proofs.M35.Uniqueness.CompleteScalarMaximum
import PoincareConjecture.Proofs.M10.ScalarBound
import PoincareConjecture.Proofs.M04.ScalarEvolution









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem raw_scalar_floor_on_slab
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) :
    ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      H.scalar_constant⁻¹ ≤ (G.flow.connection t).scalarCurvature x := by
  let c := H.scalar_constant⁻¹
  have hc : 0 < c := inv_pos.mpr H.scalar_constant_pos
  have hsub : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  have hnorm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K := (le_abs_self _).trans (hRm t ht x)
  let f : ℝ → StandardCapSpace → ℝ := fun t x => -c + (G.flow.connection t).scalarCurvature x
  have hcont : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ) :=
    continuousOn_const.add (G.flow.contMDiffOn_scalarCurvature.continuousOn.mono
      (prod_mono hsub Subset.rfl))
  have hsmooth (t : ℝ) (ht : t ∈ Ioc 0 T) (x : StandardCapSpace) :
      ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (f t) x :=
    contMDiffAt_const.add (G.flow.contMDiff_scalarCurvature t (hsub ⟨ht.1.le, ht.2⟩) x)
  have hinit (x : StandardCapSpace) : 0 ≤ f 0 x := by
    have htransport (g h : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
        D.scalarCurvature x = D'.scalarCurvature x := by
      subst h
      cases eq_of_heq hD
      rfl
    change 0 ≤ -c + (G.flow.connection 0).scalarCurvature x
    rw [htransport _ _ _ _ G.initial_metric G.initial_connection]
    dsimp only [c]
    linarith [(H.scalar_bounds x).1]
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      -(9 * K + c) ≤ f t x := by
    have hb := M10.abs_scalarCurvature_le (G.flow.metric t) (G.flow.connection t) x
    norm_num only [Nat.cast_ofNat, Nat.reducePow] at hb
    have hlow := (abs_le.mp hb).1
    change -(9 * K + c) ≤ -c + (G.flow.connection t).scalarCurvature x
    linarith [hnorm t ht x]
  have hheat (t : ℝ) (ht : t ∈ Ioc 0 T) (x : StandardCapSpace) :
      ∃ v : ℝ, HasDerivWithinAt (fun s => f s x) v (Icc 0 T) t ∧
        (G.flow.connection t).laplacian (f t) x + 0 * f t x ≤ v := by
    have hd := (P.scalar_evolution 3 StandardCapSpace _ G.flow t
      (hsub ⟨ht.1.le, ht.2⟩) x).mono hsub
    refine ⟨_, hd.const_add (-c), ?_⟩
    change (G.flow.connection t).laplacian
      (fun y => -c + (G.flow.connection t).scalarCurvature y) x + 0 * f t x ≤ _
    rw [laplacian_const_add_at _
      (G.flow.contMDiff_scalarCurvature t (hsub ⟨ht.1.le, ht.2⟩) x), zero_mul, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))))
  have h := raw_scalar_nonnegative P G hT hTlt
    (show 0 ≤ 9 * K + c by positivity) (le_refl 0) f hcont hsmooth hinit hbound hheat
  intro t ht x
  have hh := h t ht x
  change 0 ≤ -c + (G.flow.connection t).scalarCurvature x at hh
  linarith

theorem raw_scalar_floor
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) (x : StandardCapSpace) :
    H.scalar_constant⁻¹ ≤ (G.flow.connection t).scalarCurvature x := by
  let T := (t + G.lifetime) / 2
  have hT : 0 < T := by dsimp only [T]; linarith [G.lifetime_pos, ht.1]
  have hTlt : T < G.lifetime := by dsimp only [T]; linarith [ht.2]
  exact raw_scalar_floor_on_slab P H G hT hTlt t
    ⟨ht.1, by dsimp only [T]; linarith [ht.2]⟩ x

end PoincareConjecture.M35.Uniqueness
