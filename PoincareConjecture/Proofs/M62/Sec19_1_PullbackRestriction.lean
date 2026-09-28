import PoincareConjecture.Proofs.M62.Sec19_1_PullbackConnection

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullback_frozen_extension {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M} {x : ℝ}
    (hγ : ContinuousAt γ x) (v : TangentSpace (𝓡 n) (γ x)) :
    rampHorizontalCovariantDerivative D γ
        (fun s ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v (γ s)) x =
      D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
        (γ x) (curveVelocity γ x) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (γ x)
  have hnear : ∀ᶠ s in 𝓝 x, γ s ∈ e.baseSet :=
    hγ (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (γ x)))
  have heq : (fun s ↦ (e ⟨γ s, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v (γ s)⟩).2)
      =ᶠ[𝓝 x] (fun _ : ℝ ↦ (e ⟨γ x, v⟩).2) := by
    filter_upwards [hnear] with s hs
    change (e ⟨γ s, e.symm (γ s) (e ⟨γ x, v⟩).2⟩).2 = (e ⟨γ x, v⟩).2
    simpa only using congrArg Prod.snd (e.apply_mk_symm hs (e ⟨γ x, v⟩).2)
  simp only [rampHorizontalCovariantDerivative, FiberBundle.extend_apply_self]
  change e.symmL ℝ (γ x)
      (deriv (fun s ↦ (e ⟨γ s, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v (γ s)⟩).2) x) +
        D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
          (γ x) (curveVelocity γ x) = _
  rw [heq.deriv_eq, deriv_const, map_zero, zero_add]

theorem pullback_ambient_field {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {γ : ℝ → M} {x : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ x)
    (W : (p : M) → TangentSpace (𝓡 n) p)
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun p ↦ (⟨p, W p⟩ : TangentBundle (𝓡 n) M)) (γ x)) :
    rampHorizontalCovariantDerivative D γ (fun s ↦ W (γ s)) x =
      D.connection W (γ x) (curveVelocity γ x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra hne
  let A := rampHorizontalCovariantDerivative D γ (fun s ↦ W (γ s)) x
  let B := D.connection W (γ x) (curveVelocity γ x)
  let v := A - B
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun p ↦ (⟨p, Z p⟩ : TangentBundle (𝓡 n) M)) (γ x) :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hZx : Z (γ x) = v := FiberBundle.extend_apply_self _ _
  have hpair : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      (fun p ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p
        (g.inner p (W p) (Z p))) (γ x) :=
    ((g.contMDiff (γ x)).mdifferentiableAt (by simp)).clm_bundle_apply₂ hW hZ
  have hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun p ↦ g.inner p (W p) (Z p)) (γ x) := by
    rw [mdifferentiableAt_totalSpace] at hpair
    exact hpair.2
  have hchain : HasDerivAt (fun s ↦ g.inner (γ s) (W (γ s)) (Z (γ s)))
      (mvfderiv (𝓡 n) (fun p ↦ g.inner p (W p) (Z p)) (γ x) (curveVelocity γ x)) x :=
    (hf.hasMFDerivAt.comp x hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hcompat := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (curveVelocity γ x)) hW hZ
  have hvalue : mvfderiv (𝓡 n) (fun p ↦ g.inner p (W p) (Z p)) (γ x)
      (curveVelocity γ x) =
        g.inner (γ x) B (Z (γ x)) +
          g.inner (γ x) (W (γ x)) (D.connection Z (γ x) (curveVelocity γ x)) := by
    simpa only [FiberBundle.extend_apply_self] using! hcompat
  have hpull := hasDerivAt_metric_pairing D hγ (hW.comp x hγ) (hZ.comp x hγ)
  have heq := hpull.unique hchain
  rw [pullback_frozen_extension D hγ.continuousAt v, hvalue, hZx] at heq
  have hz : g.inner (γ x) v v = 0 := by
    change g.inner (γ x) (A - B) v = 0
    simp only [map_sub, sub_apply]
    exact sub_eq_zero.mpr (add_right_cancel heq)
  exact ((g.pos (γ x) v (sub_ne_zero.mpr hne)).ne') hz

end PoincareConjecture.M62
