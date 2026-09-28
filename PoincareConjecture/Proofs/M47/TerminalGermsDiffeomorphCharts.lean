import PoincareConjecture.Proofs.M47.TerminalGermsUniverseMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M P Q L : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace L]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]

omit [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] in


theorem terminalGerms_diffeomorph_chart_differential
    (d : Diffeomorph (𝓡 n) (𝓡 n) L Q ∞)
    (q : M → Q) (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q) (x : M) :
    (mfderiv (𝓡 n) (𝓡 n) d (d.symm (q x))).comp
      (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x) =
        mfderiv (𝓡 n) (𝓡 n) q x := by
  have hid : d ∘ (d.symm ∘ q) =ᶠ[𝓝 x] q :=
    Filter.Eventually.of_forall fun y => d.apply_symm_apply (q y)
  refine (mfderiv_comp x (d.mdifferentiable (by simp) _)
    ((d.symm.contMDiff.comp hq.contMDiff).mdifferentiable (by simp) x)).symm.trans ?_
  exact hid.mfderiv_eq

variable [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ P]
  [IsManifold (𝓡 n) ∞ Q] [IsManifold (𝓡 n) ∞ L]

omit [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
  [IsManifold (𝓡 n) ∞ P] in


theorem terminalGerms_diffeomorph_chart_metric
    (d : Diffeomorph (𝓡 n) (𝓡 n) L Q ∞)
    (q : M → Q) (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (gM : RiemannianMetric n M) (gQ : RiemannianMetric n Q)
    (hmetric : ∀ (x : M) (a b : TangentSpace (𝓡 n) x),
      gM.inner x a b = gQ.inner (q x)
        (mfderiv (𝓡 n) (𝓡 n) q x a) (mfderiv (𝓡 n) (𝓡 n) q x b))
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    gM.inner x a b =
      (gQ.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph).inner (d.symm (q x))
        (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x a)
        (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x b) := by
  have hd := terminalGerms_diffeomorph_chart_differential d q hq x
  change gM.inner x a b = gQ.inner (d (d.symm (q x))) _ _
  rw [d.apply_symm_apply]
  exact (hmetric x a b).trans
    (congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) => gQ.inner (q x) v w)
      (congrArg (fun A => A a) hd).symm (congrArg (fun A => A b) hd).symm)

omit [IsManifold (𝓡 n) ∞ Q] [IsManifold (𝓡 n) ∞ L] in


theorem terminalGerms_diffeomorph_fibre_compatibility
    (d : Diffeomorph (𝓡 n) (𝓡 n) L Q ∞)
    (q : M → Q) (r : P → Q)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q)
    (hr : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ r)
    (gM : RiemannianMetric n M) (gP : RiemannianMetric n P)
    (hmetric : ∀ (x : M) (y : P), q x = r y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c e : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) q x a = mfderiv (𝓡 n) (𝓡 n) r y c →
        mfderiv (𝓡 n) (𝓡 n) q x b = mfderiv (𝓡 n) (𝓡 n) r y e →
        gM.inner x a b = gP.inner y c e)
    (x : M) (y : P) (hxy : d.symm (q x) = d.symm (r y))
    (a b : TangentSpace (𝓡 n) x) (c e : TangentSpace (𝓡 n) y)
    (ha : mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x a =
      mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ r) y c)
    (hb : mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x b =
      mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ r) y e) :
    gM.inner x a b = gP.inner y c e := by
  have hdq := terminalGerms_diffeomorph_chart_differential d q hq x
  have hdr := terminalGerms_diffeomorph_chart_differential d r hr y
  apply hmetric x y (d.symm.injective hxy) a b c e
  · calc
      _ = mfderiv (𝓡 n) (𝓡 n) d (d.symm (q x))
          (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x a) :=
        (congrArg (fun A => A a) hdq).symm
      _ = mfderiv (𝓡 n) (𝓡 n) d (d.symm (r y))
          (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ r) y c) :=
        congrArg₂ (fun (z : L) (v : EuclideanSpace ℝ (Fin n)) =>
          mfderiv (𝓡 n) (𝓡 n) d z v) hxy ha
      _ = _ := congrArg (fun A => A c) hdr
  · calc
      _ = mfderiv (𝓡 n) (𝓡 n) d (d.symm (q x))
          (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ q) x b) :=
        (congrArg (fun A => A b) hdq).symm
      _ = mfderiv (𝓡 n) (𝓡 n) d (d.symm (r y))
          (mfderiv (𝓡 n) (𝓡 n) (d.symm ∘ r) y e) :=
        congrArg₂ (fun (z : L) (v : EuclideanSpace ℝ (Fin n)) =>
          mfderiv (𝓡 n) (𝓡 n) d z v) hxy hb
      _ = _ := congrArg (fun A => A e) hdr

end PoincareConjecture.M47
