import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph

noncomputable section
open Set Function TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v

set_option linter.style.haveILetI false

theorem PoincareConjecture.RiemannianMetric.exists_openFiber_diffeomorph_of_diffeomorph
    {n m k : ℕ} (hdim : n=m+k) {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g : PoincareConjecture.RiemannianMetric n M) (h : PoincareConjecture.RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n,𝓡 n⟯ N)
    (he : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w=h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w))
    {f : N → Fin k → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : Opens N)
    (hreg : ∀ x∈U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) f x)) :
    let V : Opens M := ⟨e ⁻¹' U, U.isOpen.preimage e.contMDiff.continuous⟩
    let f' := f ∘ e
    let hf' : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ f' := hf.comp e.contMDiff
    ∃ hreg' : ∀ x∈V, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) f' x),
      ∀ c : Fin k → ℝ,
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=m+k) :=
        ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
      letI := openFiberChartedSpace (m := m) hf' V hreg' c
      letI := isManifold_openFiber (m := m) hf' V hreg' c
      letI := openFiberChartedSpace (m := m) hf U hreg c
      letI := isManifold_openFiber (m := m) hf U hreg c
      let gL : RiemannianMetric m (openFiber f' V c) :=
        RiemannianMetric.Induced.pullbackMetric g (openFiberIncl f' V c)
          (contMDiff_openFiberIncl (m := m) hf' V hreg' c)
          (injective_mfderiv_openFiberIncl (m := m) hf' V hreg' c)
      let hL : RiemannianMetric m (openFiber f U c) :=
        RiemannianMetric.Induced.pullbackMetric h (openFiberIncl f U c)
          (contMDiff_openFiberIncl (m := m) hf U hreg c)
          (injective_mfderiv_openFiberIncl (m := m) hf U hreg c)
      ∃ E : openFiber f' V c ≃ₘ⟮𝓡 m,𝓡 m⟯ openFiber f U c,
        (∀ x, openFiberIncl f U c (E x)=e (openFiberIncl f' V c x)) ∧
        ∀ (x : openFiber f' V c) (v w : TangentSpace (𝓡 m) x),
          gL.inner x v w=hL.inner (E x)
            (mfderiv (𝓡 m) (𝓡 m) E x v) (mfderiv (𝓡 m) (𝓡 m) E x w) := by
  classical
  let V : Opens M := ⟨e ⁻¹' U,U.isOpen.preimage e.contMDiff.continuous⟩
  let f' := f ∘ e
  have hf' : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ f' := hf.comp e.contMDiff
  have hreg' (x : M) (hx : x∈V) :
      Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) f' x) := by
    rw [mfderiv_comp x (hf.mdifferentiable (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x)]
    exact (hreg (e x) hx).comp
      (e.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).surjective
  refine ⟨hreg', ?_⟩
  intro c
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=m+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  letI := openFiberChartedSpace (m := m) hf' V hreg' c
  letI := isManifold_openFiber (m := m) hf' V hreg' c
  letI := openFiberChartedSpace (m := m) hf U hreg c
  letI := isManifold_openFiber (m := m) hf U hreg c
  let E₀ : openFiber f' V c ≃ openFiber f U c :=
    { toFun := fun x => ⟨⟨e (openFiberIncl f' V c x),x.1.2⟩,x.2⟩
      invFun := fun y => ⟨⟨e.symm (openFiberIncl f U c y),by
        change e (e.symm (openFiberIncl f U c y))∈U
        rw [e.apply_symm_apply]
        exact y.1.2⟩,by
        change f (e (e.symm (openFiberIncl f U c y)))=c
        rw [e.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.symm_apply_apply _
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        exact e.apply_symm_apply _ }
  let E : openFiber f' V c ≃ₘ⟮𝓡 m,𝓡 m⟯ openFiber f U c :=
    { E₀ with
      contMDiff_toFun := fun x =>
        (contMDiffAt_into_openFiber_iff (m := m) hf c U hreg E₀ x).mpr
          ((e.contMDiff.comp (contMDiff_openFiberIncl (m := m) hf' V hreg' c)) x)
      contMDiff_invFun := fun x =>
        (contMDiffAt_into_openFiber_iff (m := m) hf' c V hreg' E₀.symm x).mpr
          ((e.symm.contMDiff.comp (contMDiff_openFiberIncl (m := m) hf U hreg c)) x) }
  refine ⟨E, fun _ => rfl, ?_⟩
  intro x v w
  have hchain (z : TangentSpace (𝓡 m) x) :
      mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f U c) (E x)
        (mfderiv (𝓡 m) (𝓡 m) E x z)=
      mfderiv (𝓡 n) (𝓡 n) e (openFiberIncl f' V c x)
        (mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f' V c) x z) := by
    have h₁ := mfderiv_comp x
      ((contMDiff_openFiberIncl (m := m) hf U hreg c).mdifferentiable (by simp) (E x))
      (E.contMDiff.mdifferentiable (by simp) x)
    have h₂ := mfderiv_comp x
      (e.contMDiff.mdifferentiable (by simp) (openFiberIncl f' V c x))
      ((contMDiff_openFiberIncl (m := m) hf' V hreg' c).mdifferentiable (by simp) x)
    have hfun : openFiberIncl f U c ∘ E = e ∘ openFiberIncl f' V c := rfl
    rw [hfun,h₂] at h₁
    exact (congrArg (fun A => A z) h₁).symm
  change g.inner (openFiberIncl f' V c x)
      (mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f' V c) x v)
      (mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f' V c) x w)=
    h.inner (e (openFiberIncl f' V c x))
      (mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f U c) (E x)
        (mfderiv (𝓡 m) (𝓡 m) E x v))
      (mfderiv (𝓡 m) (𝓡 n) (openFiberIncl f U c) (E x)
        (mfderiv (𝓡 m) (𝓡 m) E x w))
  rw [he,hchain,hchain]
