import PoincareConjecture.Proofs.M04.RicciRayleigh
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed
import PoincareConjecture.Definitions.M63Ramp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem continuousOn_flow_ricciRayleigh
    (F : RicciFlow n M (Icc a b))
    {Z : Type v} [TopologicalSpace Z] {A : Set Z}
    {tau : Z → ℝ} {q : Z → M}
    (Y : (z : Z) → TangentSpace (𝓡 n) (q z))
    (hTau : ContinuousOn tau A) (hTime : MapsTo tau A (Icc a b))
    (hq : ContinuousOn q A)
    (hY : ContinuousOn
      (fun z => (⟨q z, Y z⟩ : TangentBundle (𝓡 n) M)) A)
    (hYne : ∀ z ∈ A, Y z ≠ 0) :
    ContinuousOn (fun z => (F.connection (tau z)).ricci (q z) (Y z) (Y z) /
      (F.metric (tau z)).inner (q z) (Y z) (Y z)) A := by
  intro z0 hz0
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) (q z0)
  let w : Z → E := fun z => (e ⟨q z, Y z⟩).2
  let A' := A ∩ q ⁻¹' e.baseSet
  have hbase : q z0 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (q z0)
  have hz0' : z0 ∈ A' := ⟨hz0, hbase⟩
  have hw : ContinuousWithinAt w A z0 := by
    exact ((FiberBundle.continuousWithinAt_totalSpace E _).mp (hY z0 hz0)).2
  have hrecover (z : Z) (hz : q z ∈ e.baseSet) :
      e.symmL ℝ (q z) (w z) = Y z := by
    dsimp only [w]
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz]
    exact e.symmL_continuousLinearMapAt hz (Y z)
  have hwne (z : Z) (hz : z ∈ A') : w z ≠ 0 := by
    intro hzero
    have h := hrecover z hz.2
    rw [hzero, map_zero] at h
    exact hYne z hz.1 h.symm
  let P : Z → (ℝ × M) × E := fun z => ((tau z, q z), w z)
  have hP : ContinuousWithinAt P A z0 :=
    ((hTau z0 hz0).prodMk (hq z0 hz0)).prodMk hw
  have hmaps : MapsTo P A' ((Icc a b ×ˢ e.baseSet) ×ˢ {v : E | v ≠ 0}) :=
    fun z hz => ⟨⟨hTime hz.1, hz.2⟩, hwne z hz⟩
  have hR := M04.continuousOn_flow_ricciRayleigh_trivialization F (q z0)
  have hcomp := (hR (P z0) (hmaps hz0')).comp (hP.mono inter_subset_left) hmaps
  have hlocal : ContinuousWithinAt
      (fun z => (F.connection (tau z)).ricci (q z) (Y z) (Y z) /
        (F.metric (tau z)).inner (q z) (Y z) (Y z)) A' z0 := by
    apply hcomp.congr_of_mem _ hz0'
    intro z hz
    change (F.connection (tau z)).ricci (q z) (Y z) (Y z) /
        (F.metric (tau z)).inner (q z) (Y z) (Y z) =
      (F.connection (tau z)).ricci (q z) (e.symmL ℝ (q z) (w z))
          (e.symmL ℝ (q z) (w z)) /
        (F.metric (tau z)).inner (q z) (e.symmL ℝ (q z) (w z))
          (e.symmL ℝ (q z) (w z))
    rw [hrecover z hz.2]
  have hnear : A' ∈ 𝓝[A] z0 := by
    have hpre : q ⁻¹' e.baseSet ∈ 𝓝[A] z0 :=
      (hq z0 hz0) (e.open_baseSet.mem_nhds hbase)
    filter_upwards [self_mem_nhdsWithin (s := A) (a := z0), hpre] with z hz hqz
    exact ⟨hz, hqz⟩
  exact hlocal.mono_of_mem_nhdsWithin hnear

theorem c2ShrinkingCurve_speed_normalization_continuousOn
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J) :
    ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 z.1) (univ ×ˢ J) ∧
      ContinuousOn (fun z : ℝ × ℝ =>
        m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1)
        (univ ×ˢ J) := by
  have hpair (Y Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
      (hY : ContinuousOn (fun z => (⟨c z.1 z.2, Y z⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ J))
      (hZ : ContinuousOn (fun z => (⟨c z.1 z.2, Z z⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ J)) :
      ContinuousOn (fun z : ℝ × ℝ =>
        (F.metric z.2).inner (c z.1 z.2) (Y z) (Z z)) (univ ×ˢ J) := by
    have hg := F.smooth.continuousOn.comp
      (continuous_snd.continuousOn.prodMk hc.continuous)
      (fun z hz => ⟨hc.domain_subset hz.2, mem_univ _⟩)
    intro z hz
    have hp : ContinuousWithinAt
        (fun w : ℝ × ℝ => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          (c w.1 w.2) ((F.metric w.2).inner (c w.1 w.2) (Y w) (Z w)))
        (univ ×ˢ J) z :=
      (hg z hz).clm_bundle_apply₂ (hY z hz) (hZ z hz)
    exact ((FiberBundle.continuousWithinAt_totalSpace ℝ _).mp hp).2
  have hv : ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 z.1) (univ ×ˢ J) :=
    (hpair _ _ hc.velocity_continuous hc.velocity_continuous).sqrt
  have hk : ContinuousOn (fun z : ℝ × ℝ => m62CurvatureSquared F c z.2 z.1)
      (univ ×ˢ J) := hpair _ _ hc.curvature_continuous hc.curvature_continuous
  have hR := continuousOn_flow_ricciRayleigh F (A := univ ×ˢ J)
    (tau := Prod.snd) (q := fun z : ℝ × ℝ => c z.1 z.2)
    (fun z : ℝ × ℝ => curveVelocity (n := n) (fun y => c y z.2) z.1)
    continuous_snd.continuousOn (fun _ hz => hc.domain_subset hz.2)
    hc.continuous hc.velocity_continuous (fun z hz => hc.immersed z.2 hz.2 z.1)
  have hRic : ContinuousOn (fun z : ℝ × ℝ => m62TangentRicci F c z.2 z.1)
      (univ ×ˢ J) := by
    apply hR.congr
    intro z hz
    let X := curveVelocity (n := n) (fun y => c y z.2) z.1
    let S := spatialUnitTangent F c z.2 z.1
    let v := curveSpeed F c z.2 z.1
    have hvpos : 0 < v :=
      Real.sqrt_pos.mpr ((F.metric z.2).pos _ _ (hc.immersed z.2 hz.2 z.1))
    have hX : X = v • S := by
      symm
      change v • (v⁻¹ • X) = X
      rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
    obtain ⟨A, hA⟩ :=
      (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection z.2)).1 (c z.1 z.2)
    have hscale := A.map_smul_univ (fun _ : Fin 2 => v) (fun _ : Fin 2 => S)
    rw [← hA, ← hA] at hscale
    have hRicval : (F.connection z.2).ricci (c z.1 z.2) X X =
        v ^ 2 * m62TangentRicci F c z.2 z.1 := by
      rw [hX]
      simpa only [LeviCivitaData.ricciEvaluation, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, m62TangentRicci, S] using hscale
    change m62TangentRicci F c z.2 z.1 =
      (F.connection z.2).ricci (c z.1 z.2) X X / (F.metric z.2).inner (c z.1 z.2) X X
    rw [hRicval, ← M62.speed_sq F c z.2 z.1]
    change _ = v ^ 2 * _ / v ^ 2
    field_simp [hvpos.ne']
  exact ⟨hv, hRic.add hk⟩

end PoincareConjecture.M63
