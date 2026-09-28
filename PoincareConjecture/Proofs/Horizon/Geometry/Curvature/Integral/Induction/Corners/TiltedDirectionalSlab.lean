import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.DirectionalPair
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.TiltedSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology BigOperators

universe u

theorem PoincareConjecture.RiemannianMetric.exists_directional_tilted_regular_fiber_slabs
    {m k : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 1) + k))) M] [IsManifold (𝓡 ((m + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((m + 1) + k) M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 ((m + 1) + k)) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) (f h : Fin k → M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    {δold C q : ℝ} (hδold : 0 ≤ δold) (hC : 0 ≤ C) (hq : 0 < q)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δold)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 ((m + 1) + k)) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    {r Δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal (4 * r) → x ∈ U) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ (2 : ℕ) / 2048
    (4 * Real.sqrt δold + 3 * q / r + 2 * C * r + σ ^ (2 : ℕ) / 8 ≤ ε / 2) →
    (∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε) →
    (∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - σ ^ (2 : ℕ) / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) →
    let τ := 1 / (1 + σ ^ (2 : ℕ) / 8)
    let ε₀ := σ ^ (4 : ℕ) * r / 1048576
    let s := τ * r / 1024
    let I := Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))
    let a := Δ / 4
    let β := a / ((k : ℝ) + 1)
    ∃ u F : M → ℝ, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ u ∧
      ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x, F x = (1 - a) * u x + β * ∑ i, h i x) ∧
      IsProperMap (I.restrictPreimage u) ∧
      (∀ x : M, u x ∈ I → mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      (∀ x : M, u x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |u x - τ * (g.edist p x).toReal| ≤ τ * ε₀ ∧
        1 - σ ^ (2 : ℕ) ≤ g.tangentNorm x (D.gradient u x) ∧
        g.tangentNorm x (D.gradient u x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 ((m + 1) + k)) x,
          D.hessian u x v v ≤ (5 / r) * g.inner x v v) ∧
        ((∀ i, |f i x - f i p| ≤ q) → ∀ i,
          |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
          |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2)) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact (u ⁻¹' Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)) ∧
        ∃ v : M → ℝ, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ v ∧
          let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          let S := {x : M | x ∈ V ∧ ∀ i, |f i x - f i p| < q}
          let H := max C (3 / s)
          let G := fun x => (1 - a) * v x + β * ∑ i, h i x
          let f' : Fin (k + 1) → M → ℝ := Fin.cons F f
          let h' : Fin (k + 1) → M → ℝ := Fin.cons G h
          ∃ (hS : IsOpen S)
            (hregOld : ∀ x ∈ S, Function.Surjective
              (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin k → ℝ) (fun y i => f i y) x)),
          (∀ x : M, u x = 2 * τ * t → (∀ i, f i x = f i p) →
            ∀ y, g.edist x y ≤ ENNReal.ofReal (min (s / 16) (q / 2)) → y ∈ S) ∧
          (∀ x : M, u x = 2 * τ * t → ∀ y, g.edist x y ≤ ENNReal.ofReal (s / 16) → y ∈ V) ∧
          (∀ x ∈ V,
            r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient u x) ∧
            g.tangentNorm x (D.gradient u x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ g.tangentNorm x (D.gradient v x) ∧
            g.tangentNorm x (D.gradient v x) ≤ 1 ∧
            g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ (2 : ℕ) / 8 ∧
            ∀ w : TangentSpace (𝓡 ((m + 1) + k)) x,
              D.hessian u x w w ≤ (3 / s) * g.inner x w w ∧
              D.hessian v x w w ≤ (3 / s) * g.inner x w w) ∧
          (∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
          (∀ i, ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
          (∀ x ∈ S,
            (∀ i,
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
                g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
              (1 - 2 * Δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
                g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * Δ) ∧
            (∀ i j, i ≠ j →
              |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ Δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ Δ ∧
              g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
            (∀ i : Fin k,
              g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
            ∀ w : TangentSpace (𝓡 ((m + 1) + k)) x, ∀ i,
              D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
              D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
          (∀ x ∈ S, Function.Surjective
            (mfderiv (𝓡 ((m + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x)) ∧
          let b := (1 - a) * (2 * τ * t) + β * ∑ i, h i p
          let J := Ioo (b - s / 16) (b + s / 16)
          let W : TopologicalSpace.Opens M := ⟨S, hS⟩
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + k))) =
            (m + 1) + k) := ⟨by simp⟩
          letI := Poincare.Geometry.Manifold.RegularFiber.openFiberChartedSpace
            (m := m + 1) (contMDiff_pi_space.mpr hf) W hregOld (fun i => f i p)
          let incl := Poincare.Geometry.Manifold.RegularFiber.openFiberIncl
            (fun y i => f i y) W (fun i => f i p)

          ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (F ∘ incl) ∧
          IsProperMap (J.restrictPreimage (F ∘ incl)) ∧
          (∀ x, mfderiv (𝓡 (m + 1)) 𝓘(ℝ, ℝ) (F ∘ incl) x ≠ 0) ∧
          ∀ x, F (incl x) ∈ J →
            2 * τ * t - s / 6 < u (incl x) ∧
              u (incl x) < 2 * τ * t + s / 6 := by
  classical
  dsimp only
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  intro hbudget holdcross hascent
  let := g.toMetricSpace
  let τ := 1 / (1 + σ ^ 2 / 8)
  let ε₀ := σ ^ 4 * r / 1048576
  let s := τ * r / 1024
  let a := Δ / 4
  let β := a / ((k : ℝ) + 1)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨ha, ha64, hs, hmargin⟩ :=
    Poincare.CurvatureIntegral.tilted_slab_margin_of_strainer_budget
      hΔ hΔsmall hC hq.le hr hbudget
  obtain ⟨u, hu, hproper, hreg, hband, hcore, hlevels⟩ :=
    g.exists_directional_slab_with_augmented_level_strainers_in_value_tube
      D hc hsec p f h hU hf hh hδold hC hq hpair hhess htight
      hr hr1 hΔ hΔsmall hball hbudget holdcross hascent
  let F := fun x => (1 - a) * u x + β * ∑ i, h i x
  have hF : ContMDiff (𝓡 ((m + 1) + k)) 𝓘(ℝ, ℝ) ∞ F :=
    (contMDiff_const.mul hu).add (contMDiff_const.mul (ContMDiff.sum (fun i _ => hh i)))
  refine ⟨u, F, hu, hF, fun _ => rfl, hproper, hreg, hband, hcore, ?_⟩
  intro t ht
  obtain ⟨hcompact, v, hv, hopenS, hbufferS, hbufferV, hVbounds,
    hfaug, hhaug, haugBounds, haug⟩ := hlevels t ht
  let V := u ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
  let S := {x : M | x ∈ V ∧ ∀ i, |f i x - f i p| < q}
  have hstrip (x : M)
      (hx : u x ∈ Icc (2 * τ * t - s / 4) (2 * τ * t + s / 4)) :
      (g.edist p x).toReal < 2 * r := by
    exact (hband x (Poincare.CurvatureIntegral.normalized_level_strip_subset_slab hr hτ ht hx)).2
  have hpairs (i : Fin k) (x : M) (hx : g.edist p x ≤ ENNReal.ofReal (2 * r)) :
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δold :=
    hpair i x (hball x (hx.trans (ENNReal.ofReal_le_ofReal (by linarith))))
  have hjoin :
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (F y) (fun i => f i y)) =
        (fun y i => (Fin.cons (α := fun _ : Fin (k + 1) => M → ℝ) F f i) y) := by
    funext y i
    exact Fin.cases rfl (fun _ => rfl) i
  obtain ⟨hS, hregOld, hrestricted⟩ :=
    D.proper_regular_tilted_slab_on_openFiber hc f h u hf hh hu p
      hr hs hq ha ha64 hδold hmargin hcompact hstrip hpairs
      (fun x hx hxtube => by
        change Function.Surjective (mfderiv (𝓡 ((m + 1) + k))
          𝓘(ℝ, Fin (k + 1) → ℝ)
          (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (F y) (fun i => f i y)) x)
        rw [hjoin]
        exact haug x ⟨hx, hxtube⟩)
  have hmem (x y : M) {R : ℝ} (hR : 0 ≤ R)
      (hxy : g.edist x y ≤ ENNReal.ofReal R) : y ∈ Metric.closedBall x R := by
    apply Metric.mem_closedBall.mpr
    rw [dist_comm]
    change (g.edist x y).toReal ≤ R
    calc
      _ ≤ (ENNReal.ofReal R).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hxy
      _ = R := ENNReal.toReal_ofReal hR
  refine ⟨hcompact, v, hv, hS, hregOld, ?_, ?_,
    hVbounds, hfaug, hhaug, haugBounds, haug, ?_⟩
  · intro x hx hxf y hxy
    exact hbufferS x hx hxf (hmem x y (le_min (by positivity) (by positivity)) hxy)
  · intro x hx y hxy
    exact hbufferV x hx (hmem x y (by positivity) hxy)
  · exact hrestricted
