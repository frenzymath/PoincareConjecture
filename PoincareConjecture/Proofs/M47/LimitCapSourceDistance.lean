import PoincareConjecture.Proofs.M47.LimitCapSourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

private theorem finite_source_tangent_bound
    {C D : GeneralizedSliceCarrier.{u}}
    (g : RiemannianMetric 3 C.carrier) (h : RiemannianMetric 3 D.carrier)
    (x : C.carrier) (y : D.carrier)
    (v : TangentSpace (𝓡 3) x) (w : TangentSpace (𝓡 3) y)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B)
    (hbound : Q * h.inner y w w ≤ B * g.inner x v v) :
    h.tangentNorm y w ≤ (Real.sqrt B / Real.sqrt Q) * g.tangentNorm x v := by
  have hg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  change Real.sqrt (h.inner y w w) ≤
    (Real.sqrt B / Real.sqrt Q) * Real.sqrt (g.inner x v v)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, div_pow, Real.sq_sqrt hB, Real.sq_sqrt hQ.le, Real.sq_sqrt hg,
    div_mul_eq_mul_div]
  exact (le_div_iff₀ hQ).mpr (by nlinarith only [hbound])

theorem finite_source_ball_bottom_distance
    (P : M44CapPersistencePredecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} (hpinch : SurgeryFlowPinched F)
    (g : RiemannianMetric 3 C.carrier) (o : C.carrier)
    {base Q a T K R : ℝ} (hR : 0 < R) (hK : 0 ≤ K) (ha : a ∈ Icc (-T) 0)
    (e : SurgeryFlowCylinder F C base Q (Icc a 0) (g.ball o R))
    (hRm : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
      (F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x) ≤ K * Q)
    (hterminal : ∀ x ∈ g.ball o R, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner 0 ⟨ha.2, le_rfl⟩ x v v ≤ 2 * g.inner x v v) :
    ∀ contact ∈ g.ball o R, ∀ x ∈ g.ball o R,
      (F.metric (base + a / Q)).edist
        (e.forward a ⟨le_rfl, ha.2⟩ contact) (e.forward a ⟨le_rfl, ha.2⟩ x) ≤
        ENNReal.ofReal ((2 * Real.sqrt (2 * Real.exp (6 * K * T)) * R) / Real.sqrt Q) := by
  let h := F.metric (base + a / Q)
  let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2⟩
  let L := Real.sqrt (2 * Real.exp (6 * K * T))
  have hQ := e.scale_pos
  have hL : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hfactor : 0 < L / Real.sqrt Q := div_pos hL (Real.sqrt_pos.mpr hQ)
  have hU : IsOpen (g.ball o R) := M04.initial_ball_isOpen g o R
  have hquad (x : C.carrier) (hx : x ∈ g.ball o R) (v : TangentSpace (𝓡 3) x) :
      e.pullbackInner a bottom x v v ≤ 2 * Real.exp (6 * K * T) * g.inner x v v := by
    calc
      _ ≤ Real.exp (6 * K * T) * e.pullbackInner 0 ⟨ha.2, le_rfl⟩ x v v :=
        finite_source_metric_exp_upper P hpinch e hU ha hK hRm a bottom x hx v
      _ ≤ Real.exp (6 * K * T) * (2 * g.inner x v v) :=
        mul_le_mul_of_nonneg_left (hterminal x hx v) (Real.exp_pos _).le
      _ = _ := by ring
  have hnorm (x : C.carrier) (hx : x ∈ g.ball o R) (v : TangentSpace (𝓡 3) x) :
      h.tangentNorm (e.forward a bottom x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward a bottom) x v) ≤
          (L / Real.sqrt Q) * g.tangentNorm x v :=
    finite_source_tangent_bound (D := F.slice (base + a / Q)) g h x
      (e.forward a bottom x) v (mfderiv (𝓡 3) (𝓡 3) (e.forward a bottom) x v)
      hQ (by positivity) (hquad x hx v)
  have himage := g.image_ball_subset_ball_of_tangentNorm_le_on_open h
    (e.forward a bottom) hU ((e.forward_smooth a bottom).of_le (by simp)) hfactor
      hnorm (Subset.refl (g.ball o R)) (le_rfl : (L / Real.sqrt Q) * R ≤ _)
  intro contact hcontact x hx
  have hc := himage (mem_image_of_mem _ hcontact)
  have hx' := himage (mem_image_of_mem _ hx)
  change h.edist (e.forward a bottom o) (e.forward a bottom contact) <
    ENNReal.ofReal ((L / Real.sqrt Q) * R) at hc
  change h.edist (e.forward a bottom o) (e.forward a bottom x) <
    ENNReal.ofReal ((L / Real.sqrt Q) * R) at hx'
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice (base + a / Q)).carrier →
      Type _) := ⟨h.toRiemannianMetric⟩
  have hreverse : h.edist (e.forward a bottom contact) (e.forward a bottom o) =
      h.edist (e.forward a bottom o) (e.forward a bottom contact) :=
    Manifold.riemannianEDist_comm
  calc
    _ ≤ h.edist (e.forward a bottom contact) (e.forward a bottom o) +
        h.edist (e.forward a bottom o) (e.forward a bottom x) :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((L / Real.sqrt Q) * R) +
        ENNReal.ofReal ((L / Real.sqrt Q) * R) := by
      rw [hreverse]
      exact add_le_add hc.le hx'.le
    _ = ENNReal.ofReal ((2 * L * R) / Real.sqrt Q) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end PoincareConjecture.M47
