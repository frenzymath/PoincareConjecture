import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.ProductIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.EuclideanSpace
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]



noncomputable def productVolumeChart
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M :=
  let H := (euclideanConsCLE n).symm.toHomeomorph.trans (Homeomorph.prodComm _ _)
  (H.toOpenPartialHomeomorph.trans (c.prod (OpenPartialHomeomorph.refl ℝ))).trans
    e.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem productVolumeChart_apply
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    productVolumeChart e c x = e (c (euclideanTail x), x 0) := rfl

@[simp] theorem productVolumeChart_symm_apply
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N) (x : M) :
    (productVolumeChart e c).symm x =
      euclideanCons (e.symm x).2 (c.symm (e.symm x).1) := rfl

@[simp] theorem productVolumeChart_source
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N) :
    (productVolumeChart e c).source = euclideanTail ⁻¹' c.source := by
  ext x
  simp [productVolumeChart]

@[simp] theorem productVolumeChart_target
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N) :
    (productVolumeChart e c).target = e '' (c.target ×ˢ (univ : Set ℝ)) := by
  ext x
  simp only [productVolumeChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, univ_inter,
    OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target,
    preimage_univ, inter_univ, mem_preimage]
  change (e.symm x).1 ∈ c.target ∧ (e.symm x).2 ∈ (univ : Set ℝ) ↔ _
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

theorem contMDiffOn_productVolumeChart
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source) :
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (productVolumeChart e c) (productVolumeChart e c).source := by
  intro x hx
  have hx' : euclideanTail x ∈ c.source := by simpa using hx
  have hc' := (hc _ hx').contMDiffAt (c.open_source.mem_nhds hx')
  have ht := (contDiff_euclideanTail n).contMDiff.contMDiffAt (x := x)
  have h0 : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ (fun y => y 0) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) 0).contDiff.contMDiff.contMDiffAt
  exact ((e.contMDiff.contMDiffAt.comp x ((hc'.comp x ht).prodMk h0))).contMDiffWithinAt

theorem contMDiffOn_productVolumeChart_symm
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target) :
    ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (productVolumeChart e c).symm (productVolumeChart e c).target := by
  intro x hx
  have hx' : (e.symm x).1 ∈ c.target := by
    rw [productVolumeChart_target] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa using hz.1
  have hc' := (hc _ hx').contMDiffAt (c.open_target.mem_nhds hx')
  have hi := e.symm.contMDiff.contMDiffAt (x := x)
  have hp := hi.snd.prodMk_space (hc'.comp x hi.fst)
  exact ((euclideanConsCLE n).contDiff.contMDiff.contMDiffAt.comp x hp).contMDiffWithinAt

theorem mfderiv_productVolumeChart
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (euclideanTail x))
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (productVolumeChart e c) x v =
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e
        (c (euclideanTail x), x 0)
        (mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x) (euclideanTail v), v 0) := by
  have ht : MDifferentiableAt (𝓡 (n + 1)) (𝓡 n) euclideanTail x :=
    (contDiff_euclideanTail n).contMDiff.mdifferentiable (by simp) x
  have h0 : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (fun y => y 0) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) 0).differentiableAt.mdifferentiableAt
  change mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
    (e ∘ fun y => (c (euclideanTail y), y 0)) x v = _
  erw [mfderiv_comp_apply x (e.contMDiff.mdifferentiable (by simp) _) ((hc.comp x ht).prodMk h0),
    mfderiv_prodMk (hc.comp x ht) h0]
  congr 1
  apply Prod.ext
  · change mfderiv (𝓡 (n + 1)) (𝓡 n) (c ∘ euclideanTail) x v = _
    erw [mfderiv_comp_apply x hc ht, mfderiv_eq_fderiv]
    change mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x)
      (fderiv ℝ (euclideanTailProjectionCLM n) x v) = _
    rw [(euclideanTailProjectionCLM n).fderiv]
    rfl
  · change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) 0) x v = _
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl

variable [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 (n + 1)) ∞ M]



theorem pullbackVolumeDensity_productVolumeChart
    (h : RiemannianMetric n N) (g : RiemannianMetric (n + 1) M)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
    (hmetric : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
          h.inner z.1 v.1 w.1 + v.2 * w.2)
    (c : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) N)
    (hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source)
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ (productVolumeChart e c).source) :
    g.pullbackVolumeDensity (productVolumeChart e c) x =
      h.pullbackVolumeDensity c (euclideanTail x) := by
  classical
  have hx' : euclideanTail x ∈ c.source := by simpa using hx
  have hc' := ((hc _ hx').contMDiffAt (c.open_source.mem_nhds hx')).mdifferentiableAt (by simp)
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let A := Matrix.of (fun i j : Fin (n + 1) =>
    g.inner (productVolumeChart e c x)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (productVolumeChart e c) x (b i))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (productVolumeChart e c) x (b j)))
  have hA (i j : Fin (n + 1)) : A i j =
      h.inner (c (euclideanTail x))
        (mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x) (euclideanTail (b i)))
        (mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x) (euclideanTail (b j))) +
          b i 0 * b j 0 := by
    dsimp only [A, Matrix.of_apply]
    rw [mfderiv_productVolumeChart e c hc', mfderiv_productVolumeChart e c hc']
    exact hmetric _ _ _
  have hb0 : euclideanTail (b 0) = 0 := by
    ext i
    simp [b, EuclideanSpace.basisFun_apply]
  have hbs (i : Fin n) : euclideanTail (b i.succ) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    ext j
    simp [b, EuclideanSpace.basisFun_apply]
  have hA00 : A 0 0 = 1 := by
    rw [hA, hb0]
    simp [b, EuclideanSpace.basisFun_apply]
  have hA0s (j : Fin n) : A 0 j.succ = 0 := by
    rw [hA, hb0]
    simp [b, EuclideanSpace.basisFun_apply]
  have hAss : A.submatrix Fin.succ Fin.succ = Matrix.of (fun i j : Fin n =>
      h.inner (c (euclideanTail x))
        (mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x) (EuclideanSpace.basisFun (Fin n) ℝ i))
        (mfderiv (𝓡 n) (𝓡 n) c (euclideanTail x) (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hA, hbs]
    simp [b, EuclideanSpace.basisFun_apply]
  change Real.sqrt A.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [hA00, hA0s, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rw [hAss]
  rfl

end PoincareConjecture.RiemannianMetric
