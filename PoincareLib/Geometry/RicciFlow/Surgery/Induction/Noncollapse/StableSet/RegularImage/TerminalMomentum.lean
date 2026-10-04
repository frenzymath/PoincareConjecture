import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.RegularImage.ActionContact

/-!
# Terminal momentum at a differentiable minimum-action endpoint

Morgan--Tian Claim 6.68, printed p. 140, using the first variation
formula of Lemma 6.22. The actual terminal square velocity is transported
to the genuine target slice. Outside the exponential critical image,
the contact differential determines its pairing with every target
tangent vector. The minimum action need only be differentiable at the
selected endpoint.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

/-- The selected square path ends at the actual survival-slice endpoint,
Definition 6.17 and Lemma 6.22, pp. 113-116. -/
theorem survival_square_endpoint
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) :
    (E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).curve
      (Real.sqrt tau) = (survivalSliceMap E tau htau.le q0 Z).val := by
  have hs : Real.sqrt tau ∈ M14SqrtParameterInterval 0 ((Real.sqrt tau) ^ 2) := by
    exact ⟨by simp, by rw [Real.sqrt_sq (Real.sqrt_nonneg tau)]⟩
  exact ((E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).agrees _ hs).trans
    ((E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).curve_end.trans
      (survivalSliceMap_val E htau.le q0 hZ).symm)

/-- The actual terminal momentum, placed in the horizontal tangent
space of the actual slice endpoint, Lemma 6.22, pp. 115-116. -/
noncomputable def survivalTerminalVelocity
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    (Z : G.Horizontal x) (hZ : (Z, Real.sqrt tau) ∈ E.domain) :
    G.Horizontal (survivalSliceMap E tau htau.le q0 Z).val :=
  survival_square_endpoint E htau q0 hZ ▸
    (E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).horizontal_velocity
      (Real.sqrt tau)

private theorem horizontal_inner_transport {a b : G.Point} (h : a = b)
    (v w : G.Horizontal a) :
    G.spacetime.horizontalMetric.inner b (h ▸ v) (h ▸ w) =
      G.spacetime.horizontalMetric.inner a v w := by
  cases h
  rfl

private theorem horizontal_transport_val {a b : G.Point} (h : a = b)
    (v : G.Horizontal a) :
    (show SpacetimeModelVector n from (h ▸ v : G.Horizontal b).val) = v.val := by
  cases h
  rfl

private theorem transport_terminalVelocity
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (h : (E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).curve
      (Real.sqrt tau) = E.gamma Z (Real.sqrt tau)) :
    (survivalSliceMap_val E htau.le q0 hZ) ▸ survivalTerminalVelocity E htau q0 Z hZ =
      h ▸ (E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)).horizontal_velocity
        (Real.sqrt tau) := by
  apply Subtype.ext
  simp only [survivalTerminalVelocity, horizontal_transport_val]
  rfl

/-- The actual branch-action derivative is the terminal-velocity pairing
after passing to the genuine target slice, Lemma 6.22, pp. 115-116. -/
theorem survival_action_differential
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain) (W : G.Horizontal x) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨metric⟩
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ))
        (fun V => E.action V (Real.sqrt tau)) Z W =
      G.spacetime.horizontalMetric.inner (survivalSliceMap E tau htau.le q0 Z).val
        (survivalTerminalVelocity E htau q0 Z hZ)
        ((G.slices (T - tau)).tangentEquiv (survivalSliceMap E tau htau.le q0 Z)
          (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
            (survivalSliceMap E tau htau.le q0) Z W)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨h, hfirst⟩ := (LG.exponential.action_differential T x E).2 Z
    (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau) |>.2 W
  let v := (G.slices (T - tau)).tangentEquiv (survivalSliceMap E tau htau.le q0 Z)
    (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
      (survivalSliceMap E tau htau.le q0) Z W)
  have hv : (survivalSliceMap_val E htau.le q0 hZ) ▸ v =
      E.differential Z (Real.sqrt tau) hZ W := by
    apply Subtype.ext
    exact (horizontal_transport_val _ v).trans
      (survivalSliceMap_differential E htau.le q0 hZ W)
  have hmetric := horizontal_inner_transport (survivalSliceMap_val E htau.le q0 hZ)
    (survivalTerminalVelocity E htau q0 Z hZ) v
  rw [transport_terminalVelocity E htau q0 hZ h, hv] at hmetric
  exact hfirst.trans hmetric

/-- At a noncritical minimizing branch, the single endpoint differential
of minimum action determines every terminal momentum pairing,
Claim 6.68, p. 140. -/
theorem minimizing_endpoint_momentum
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    (hattained : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (hcenter : survivalSliceMap E tau htau.le q0 Z ∈ A)
    (hmin : M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)))
    (hbij : Function.Bijective (E.differential Z (Real.sqrt tau) hZ))
    (hlength : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
      (survivalSliceMap E tau htau.le q0 Z))
    (v : TangentSpace (𝓡 n) (survivalSliceMap E tau htau.le q0 Z)) :
    mfderiv (𝓡 n) (𝓘(ℝ, ℝ))
        (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
        (survivalSliceMap E tau htau.le q0 Z) v =
      G.spacetime.horizontalMetric.inner (survivalSliceMap E tau htau.le q0 Z).val
        (survivalTerminalVelocity E htau q0 Z hZ)
        ((G.slices (T - tau)).tangentEquiv (survivalSliceMap E tau htau.le q0 Z) v) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hslice := (survivalSliceMap_differential_bijective_iff E htau.le q0 hZ).mpr hbij
  obtain ⟨W, hW⟩ := hslice.surjective v
  have hcontact := congrArg (fun L : G.Horizontal x →L[ℝ] ℝ => L W)
    (minimizing_action_contact_differential LG E htau q0 hA hattained hZ hcenter hmin hlength)
  have hfirst := survival_action_differential LG E htau q0 hZ W
  dsimp only at hfirst
  change mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ))
      (fun V => E.action V (Real.sqrt tau)) Z W =
    mfderiv (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
      (survivalSliceMap E tau htau.le q0 Z)
      (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n)
        (survivalSliceMap E tau htau.le q0) Z W) at hcontact
  rw [hW] at hcontact
  rw [hW] at hfirst
  exact hcontact.symm.trans hfirst

private theorem horizontal_eq_of_pairings (q : G.Point) (v w : G.Horizontal q)
    (h : ∀ z : G.Horizontal q,
      G.spacetime.horizontalMetric.inner q v z =
        G.spacetime.horizontalMetric.inner q w z) : v = w := by
  have hzero : G.spacetime.horizontalMetric.inner q (v - w) (v - w) = 0 := by
    simp only [map_sub, sub_apply, h, sub_self]
  by_contra hne
  exact (G.spacetime.horizontalMetric.pos q (v - w) (sub_ne_zero.mpr hne)).ne' hzero

private theorem slice_momenta_heq {t : ℝ} {q1 q2 : (G.slices t).Point}
    (hpoint : q1 = q2) (v1 : G.Horizontal q1.val) (v2 : G.Horizontal q2.val)
    (L : (G.slices t).Point → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (h1 : ∀ v, L q1 v = G.spacetime.horizontalMetric.inner q1.val v1
      ((G.slices t).tangentEquiv q1 v))
    (h2 : ∀ v, L q2 v = G.spacetime.horizontalMetric.inner q2.val v2
      ((G.slices t).tangentEquiv q2 v)) : HEq v1 v2 := by
  cases hpoint
  apply heq_of_eq
  apply horizontal_eq_of_pairings
  intro z
  obtain ⟨v, rfl⟩ := (G.slices t).tangentEquiv q1 |>.surjective z
  exact (h1 v).symm.trans (h2 v)

/-- Every two noncritical minimizing branches to the same differentiable
endpoint have the same actual terminal momentum, Claim 6.68, p. 140. -/
theorem minimizing_terminal_velocities_heq
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    (hattained : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    {Z W : G.Horizontal x}
    (hZ : (Z, Real.sqrt tau) ∈ E.domain) (hW : (W, Real.sqrt tau) ∈ E.domain)
    (hcenter : survivalSliceMap E tau htau.le q0 Z ∈ A)
    (hpoint : survivalSliceMap E tau htau.le q0 Z = survivalSliceMap E tau htau.le q0 W)
    (hminZ : M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)))
    (hminW : M14IsMinimizing (E.path W (Real.sqrt tau) hW (Real.sqrt_pos.mpr htau)))
    (hbijZ : Function.Bijective (E.differential Z (Real.sqrt tau) hZ))
    (hbijW : Function.Bijective (E.differential W (Real.sqrt tau) hW))
    (hlength : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
      (survivalSliceMap E tau htau.le q0 Z)) :
    HEq (survivalTerminalVelocity E htau q0 Z hZ)
      (survivalTerminalVelocity E htau q0 W hW) := by
  apply slice_momenta_heq hpoint
    (survivalTerminalVelocity E htau q0 Z hZ) (survivalTerminalVelocity E htau q0 W hW)
    (fun q => mfderiv (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) q)
  · exact minimizing_endpoint_momentum LG E htau q0 hA hattained hZ hcenter hminZ hbijZ hlength
  · exact minimizing_endpoint_momentum LG E htau q0 hA hattained hW
      (hpoint ▸ hcenter) hminW hbijW (hpoint ▸ hlength)

end PoincareMT.Proofs.M46
