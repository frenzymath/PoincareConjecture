import PoincareConjecture.Proofs.M47.TerminalGermsFiniteDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalGerms_metric_additional_chart
    {n : ℕ} {ι : Type*} {P : ι → Type*} {M N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace M] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g : ∀ i, RiemannianMetric n (P i))
    (h : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hpres : ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      (g i).inner x a b = gN.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (r : M → N)
    (hinv : ∀ i (y : M) (x : P i), r y = q i x →
      ∀ (a b : TangentSpace (𝓡 n) y) (c d : TangentSpace (𝓡 n) x),
        mfderiv (𝓡 n) (𝓡 n) r y a = mfderiv (𝓡 n) (𝓡 n) (q i) x c →
        mfderiv (𝓡 n) (𝓡 n) r y b = mfderiv (𝓡 n) (𝓡 n) (q i) x d →
        h.inner y a b = (g i).inner x c d)
    (y : M) (a b : TangentSpace (𝓡 n) y) :
    h.inner y a b = gN.inner (r y)
      (mfderiv (𝓡 n) (𝓡 n) r y a) (mfderiv (𝓡 n) (𝓡 n) r y b) := by
  obtain ⟨i, x, hx⟩ := hcover (r y)
  let L := (hq i).mfderivToContinuousLinearEquiv (by simp) x
  let c := L.symm (mfderiv (𝓡 n) (𝓡 n) r y a)
  let d := L.symm (mfderiv (𝓡 n) (𝓡 n) r y b)
  have hc : mfderiv (𝓡 n) (𝓡 n) (q i) x c =
      mfderiv (𝓡 n) (𝓡 n) r y a := L.apply_symm_apply _
  have hd : mfderiv (𝓡 n) (𝓡 n) (q i) x d =
      mfderiv (𝓡 n) (𝓡 n) r y b := L.apply_symm_apply _
  calc
    _ = (g i).inner x c d := hinv i y x hx.symm a b c d hc.symm hd.symm
    _ = gN.inner (q i x) _ _ := hpres i x c d
    _ = gN.inner (r y) _ _ := congrArg
      (fun z : N => gN.inner z (mfderiv (𝓡 n) (𝓡 n) (q i) x c)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x d)) hx
    _ = _ := congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) => gN.inner (r y) v w) hc hd

end PoincareConjecture.M47
