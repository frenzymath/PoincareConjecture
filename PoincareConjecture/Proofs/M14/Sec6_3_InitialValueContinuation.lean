import PoincareConjecture.Proofs.M14.Sec6_3_LocalEulerPath
import PoincareConjecture.Proofs.M14.Sec6_3_InitialValuePasting
import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueRestriction
import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueUnique










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}





theorem exists_initialValuePath_extension_neighborhood
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) :
    ∃ r : ℝ, Real.sqrt τ ≤ r ∧
      Icc 0 r ∈ 𝓝[{s | 0 ≤ s ∧ T - s ^ 2 ∈ I.domain}] (Real.sqrt τ) ∧
      ∃ z : G.Point, ∃ Q : M14SquareRootInitialValuePath G T (r ^ 2) x z Z,
        EqOn Q.square_path.curve P.square_path.curve (M14SqrtParameterInterval 0 τ) := by
  have hτ : 0 < τ := P.path.tau_lt
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hT : T ∈ I.domain := by
    rw [← G.spacetime.time_range]
    refine ⟨x, ?_⟩
    simpa only [GeneralizedFlowSpacetime.timeFunction, sub_zero] using P.path.base_time
  have hsC : Real.sqrt τ ∈ M14SqrtParameterInterval 0 τ := by
    exact ⟨by simpa only [Real.sqrt_zero] using hs.le, le_rfl⟩
  obtain ⟨l, r, hl, hls, hsr, hnear, x', y', p, R, E, hEuler, hpoint, hvel⟩ :=
    exists_squareRootEulerPath_through_velocity hM04 hM12 hT hs
      (P.square_path.curve (Real.sqrt τ)) (P.square_path.curve_time _ hsC)
      (P.square_path.horizontal_velocity (Real.sqrt τ))
  have hr : 0 < r := hs.trans_le hsr
  have hC : M14SqrtParameterInterval (l ^ 2) (r ^ 2) = Icc l r := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl.le, Real.sqrt_sq hr.le]
  have hsubP : Icc l (Real.sqrt τ) ⊆ M14SqrtParameterInterval 0 τ := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      Icc_subset_Icc hl.le (le_refl (Real.sqrt τ))
  have hsubR : Icc l (Real.sqrt τ) ⊆ M14SqrtParameterInterval (l ^ 2) (r ^ 2) := by
    rw [hC]
    exact Icc_subset_Icc le_rfl hsr
  have heq : EqOn P.square_path.curve R.curve (Icc l (Real.sqrt τ)) := by
    have h := squareRootEuler_unique hM04 hM12 R P.square_path hls hsubR hsubP
      E P.extension (fun s hs' => hEuler s (hsubR hs'))
      (fun s hs' => P.euler s (hsubP hs')) ⟨hls.le, le_rfl⟩ hpoint hvel
    exact fun s hs' => (h s hs').1.symm
  let c := (l + Real.sqrt τ) / 2
  have hlc : l < c := by dsimp only [c]; linarith
  have hcs : c < Real.sqrt τ := by dsimp only [c]; linarith
  have hc : 0 < c := hl.trans hlc
  have hctau : c ^ 2 < τ := by
    have h := (sq_lt_sq₀ hc.le hs.le).mpr hcs
    rwa [Real.sq_sqrt hτ.le] at h
  let P₀ := initialValuePathRestrict P (sq_pos_of_pos hc) hctau.le
  have hoverlap : EqOn P₀.square_path.curve R.curve
      (M14SqrtParameterInterval (l ^ 2) (c ^ 2)) := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl.le, Real.sqrt_sq hc.le]
    exact fun s hs' => heq ⟨hs'.1, hs'.2.trans hcs.le⟩
  obtain ⟨z, Q, _, _⟩ := exists_initialValuePath_of_overlap hM12 P₀ R E hEuler
    ((sq_lt_sq₀ hl.le hc.le).mpr hlc) ((sq_lt_sq₀ hc.le hr.le).mpr (hcs.trans_le hsr))
    hoverlap
  have htaur : τ ≤ r ^ 2 := by
    have h := (sq_le_sq₀ hs.le hr.le).mpr hsr
    rwa [Real.sq_sqrt hτ.le] at h
  have hsame := initialValuePath_square_eqOn hM04 hM12 Q P
  rw [min_eq_right htaur] at hsame
  exact ⟨r, hsr, mem_of_superset hnear (Icc_subset_Icc hl.le le_rfl), z, Q, hsame⟩

end PoincareConjecture.M14
