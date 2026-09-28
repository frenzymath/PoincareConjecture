import PoincareConjecture.Proofs.M14.Sec6_3_CornerStationarity
import PoincareConjecture.Proofs.M14.Sec6_3_MeetingVariations









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}

private theorem horizontal_heq_of_val_eq {z z' : G.Point} (h : z = z')
    {v : G.Horizontal z} {w : G.Horizontal z'} (hv : v.val = w.val) : HEq v w := by
  cases h
  exact heq_of_eq (Subtype.ext hv)

private theorem horizontal_transport_heq {z z' : G.Point} (h : z = z')
    (v : G.Horizontal z) : HEq v (h ▸ v : G.Horizontal z') := by
  cases h
  rfl

private theorem horizontal_inner_heq {z z' : G.Point} (h : z = z')
    {v w : G.Horizontal z} {v' w' : G.Horizontal z'} (hv : HEq v v') (hw : HEq w w') :
    G.spacetime.horizontalMetric.inner z v w = G.spacetime.horizontalMetric.inner z' v' w' := by
  cases h
  cases hv
  cases hw
  rfl




theorem squareVelocity_eq_of_minimizing_corner
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (hmin : M14IsMinimizing q)
    (p : M14BackwardPath G T a c x (q.curve c)) (hc : c < b)
    (haction : M14BackwardLAction G p =
      M14BackwardLAction G (prefixPath q c p.tau_lt hc.le))
    (Rp : M14SquareRootPath G p) (Rq : M14SquareRootPath G q)
    (Ep : M14PullbackExtension G Rp.curve (M14SqrtParameterInterval a c)
      Rp.horizontal_velocity)
    (Eq : M14PullbackExtension G Rq.curve (M14SqrtParameterInterval a b)
      Rq.horizontal_velocity)
    (hEp : ∀ s ∈ M14SqrtParameterInterval a c, ∀ W,
      M14SquareRootEulerResidual G Rp Ep s W = 0)
    (hEq : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G Rq Eq s W = 0) :
    HEq (Rp.horizontal_velocity (Real.sqrt c)) (Rq.horizontal_velocity (Real.sqrt c)) := by
  have hc0 : 0 ≤ c := p.tau_nonneg.trans p.tau_lt.le
  have hsp : Real.sqrt c ∈ M14SqrtParameterInterval a c :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hsq : Real.sqrt c ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, Real.sqrt_le_sqrt hc.le⟩
  have hpoint : Rp.curve (Real.sqrt c) = Rq.curve (Real.sqrt c) := by
    rw [Rp.agrees _ hsp, Rq.agrees _ hsq, Real.sq_sqrt hc0, p.curve_end]
  let A : G.Horizontal (Rq.curve (Real.sqrt c)) := hpoint ▸ Rp.horizontal_velocity (Real.sqrt c)
  let B := Rq.horizontal_velocity (Real.sqrt c)
  let D := A - B
  have hA : HEq (Rp.horizontal_velocity (Real.sqrt c)) A :=
    horizontal_transport_heq hpoint _
  obtain ⟨j, U, lift, hU, hqU, hlift, hright, _⟩ :=
    exists_smooth_gauge_lift G (Rq.curve (Real.sqrt c))
  obtain ⟨V, hV⟩ : ∃ V : G.Horizontal
      ((G.gaugeCover.cylinder j).toSpacetime (lift (Rq.curve (Real.sqrt c)))), V.val = D.val := by
    rw [hright _ hqU]
    exact ⟨D, rfl⟩
  obtain ⟨w, hw⟩ := ((G.gaugeCover.metric j).spatialTangentEquiv
    (lift (Rq.curve (Real.sqrt c))).1 (lift (Rq.curve (Real.sqrt c))).2).surjective V
  obtain ⟨Vp, Vq, hleft, hfix, hjoin, hpfield, hqfield⟩ :=
    exists_meetingGauge_variations hM12 q p hc Rp Rq j lift hU hlift hright hqU w
  have hval := (congrArg Subtype.val hw).trans hV
  have hVp : HEq (M14VariationField Vp (Real.sqrt c)) D :=
    horizontal_heq_of_val_eq hpoint (hpfield.trans hval)
  have hVq : M14VariationField Vq (Real.sqrt c) = D := Subtype.ext (hqfield.trans hval)
  have hpair := cornerVariation_momentum_pairing hCoordinates hM12 q hmin p hc haction
    Rp Rq Ep Eq hEp hEq Vp Vq hleft hfix hjoin
  rw [horizontal_inner_heq hpoint hA hVp, hVq] at hpair
  have hzero : G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c)) D D = 0 := by
    calc
      _ = G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c)) A D -
          G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c)) B D :=
        congrArg (fun L : G.Horizontal (Rq.curve (Real.sqrt c)) →L[ℝ] ℝ => L D)
          ((G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c))).map_sub A B)
      _ = 0 := sub_eq_zero.mpr hpair
  have hAB : A = B := by
    by_contra hne
    exact (ne_of_gt (G.spacetime.horizontalMetric.pos (Rq.curve (Real.sqrt c)) D
      (sub_ne_zero.mpr hne))) hzero
  exact hA.trans (heq_of_eq hAB)

end PoincareConjecture.M14
