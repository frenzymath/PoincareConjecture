import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConvexCornerArrival

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

theorem m64Intrinsic_interior_geodesic_arrival_strict_corner
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta eta : ℝ → AnnulusCoordinates} {A B u T : ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta) (he : ContDiff ℝ ∞ eta)
    (hA : 0 < A) (hB : 0 < B) (huT : u < T)
    (hageo : G.IsGeodesicOn alpha (Icc 0 A))
    (hbgeo : G.IsGeodesicOn beta (Icc 0 B))
    (hegeo : G.IsGeodesicOn eta (Icc u T))
    (hmeetA : eta T = alpha A) (hmeetB : eta T = beta B)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hsideA : MapsTo alpha (Icc 0 A) (frontier U))
    (hsideB : MapsTo beta (Icc 0 B) (frontier U))
    (hinside : MapsTo eta (Ioo u T) U) (hereg : deriv eta T ≠ 0)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (eta T))
    (hzero : phi (eta T) = 0)
    (haxisA : L.symm (1, 0) = -deriv alpha A)
    (haxisB : L.symm (0, 1) = -deriv beta B)
    (hcorner : ∀ᶠ z in 𝓝 (eta T), z ∈ closure U → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    0 < (L (-deriv eta T)).1 ∧ 0 < (L (-deriv eta T)).2 ∧
      LinearIndependent ℝ (![-deriv alpha A, -deriv eta T] :
        Fin 2 → AnnulusCoordinates) ∧
      LinearIndependent ℝ (![-deriv beta B, -deriv eta T] :
        Fin 2 → AnnulusCoordinates) := by
  let w := -deriv eta T
  have hw : w ≠ 0 := neg_ne_zero.mpr hereg
  have hnonneg : 0 ≤ (L w).1 ∧ 0 ≤ (L w).2 :=
    m64Intrinsic_convex_corner_arrival_nonneg he huT
      (fun t ht => subset_closure (hinside ht)) L hphi hzero hcorner
  have hnotzero : ¬ ((L w).1 = 0 ∧ (L w).2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hw
    apply L.injective
    ext <;> simp [h1, h2]
  have hpos1 : 0 < (L w).1 := by
    by_contra hn
    have hz1 : (L w).1 = 0 := le_antisymm (le_of_not_gt hn) hnonneg.1
    have hp2 : 0 < (L w).2 := lt_of_le_of_ne hnonneg.2
      (fun hz2 => hnotzero ⟨hz1, hz2.symm⟩)
    have hcoeff : w = (L w).2 • (-deriv beta B) := by
      apply L.injective
      rw [← haxisB, map_smul, L.apply_symm_apply]
      ext <;> simp [hz1]
    have hvel : deriv eta T = (L w).2 • deriv beta B := by
      simpa only [w, smul_neg, neg_neg] using congrArg Neg.neg hcoeff
    exact m64Intrinsic_interior_geodesic_arrival_not_positive_multiple G hb hB huT hp2
      hbgeo hegeo hmeetB hU hsideB hinside hvel
  have hpos2 : 0 < (L w).2 := by
    by_contra hn
    have hz2 : (L w).2 = 0 := le_antisymm (le_of_not_gt hn) hnonneg.2
    have hcoeff : w = (L w).1 • (-deriv alpha A) := by
      apply L.injective
      rw [← haxisA, map_smul, L.apply_symm_apply]
      ext <;> simp [hz2]
    have hvel : deriv eta T = (L w).1 • deriv alpha A := by
      simpa only [w, smul_neg, neg_neg] using congrArg Neg.neg hcoeff
    exact m64Intrinsic_interior_geodesic_arrival_not_positive_multiple G ha hA huT hpos1
      hageo hegeo hmeetA hU hsideA hinside hvel
  refine ⟨hpos1, hpos2, ?_, ?_⟩
  · rw [linearIndependent_fin2]
    refine ⟨hw, ?_⟩
    intro c hc
    change c • w = -deriv alpha A at hc
    have hcoord : c * (L w).2 = 0 := by
      have h : c • L w = (1, 0) := by
        rw [← map_smul, hc, ← haxisA, L.apply_symm_apply]
      exact congrArg Prod.snd h
    have hc0 := (mul_eq_zero.mp hcoord).resolve_right hpos2.ne'
    have h := congrArg (fun v : AnnulusCoordinates => (L v).1) hc
    simp [hc0, ← haxisA] at h
  · rw [linearIndependent_fin2]
    refine ⟨hw, ?_⟩
    intro c hc
    change c • w = -deriv beta B at hc
    have hcoord : c * (L w).1 = 0 := by
      have h : c • L w = (0, 1) := by
        rw [← map_smul, hc, ← haxisB, L.apply_symm_apply]
      exact congrArg Prod.fst h
    have hc0 := (mul_eq_zero.mp hcoord).resolve_right hpos1.ne'
    have h := congrArg (fun v : AnnulusCoordinates => (L v).2) hc
    simp [hc0, ← haxisB] at h

end PoincareConjecture
