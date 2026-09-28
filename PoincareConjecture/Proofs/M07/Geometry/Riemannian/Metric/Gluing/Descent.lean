import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.InducedForm
import Mathlib.Geometry.Manifold.LocalDiffeomorph









open PoincareConjecture Bundle
open scoped ContDiff Manifold Topology








noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Poincare.Gluing
universe u v w z

theorem exists_unique_metric_of_covering_local_diffeomorphisms
    {n : ℕ}
    {A : Type v} {P : A -> Type w}
    [forall i, TopologicalSpace (P i)]
    [forall i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [forall i, IsManifold (𝓡 n) ∞ (P i)]
    {N : Type z} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    (g : forall i, RiemannianMetric n (P i))
    (q : forall i, P i -> N)
    (hq : forall i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : forall y, ∃ i x, q i x = y)
    (hinv : forall i j (p : P i) (p' : P j), q i p = q j p' ->
      forall (a b : TangentSpace (𝓡 n) p)
        (a' b' : TangentSpace (𝓡 n) p'),
        mfderiv (𝓡 n) (𝓡 n) (q i) p a =
          mfderiv (𝓡 n) (𝓡 n) (q j) p' a' ->
        mfderiv (𝓡 n) (𝓡 n) (q i) p b =
          mfderiv (𝓡 n) (𝓡 n) (q j) p' b' ->
        (g i).inner p a b = (g j).inner p' a' b') :
    ∃! gN : RiemannianMetric n N,
      forall i (p : P i) (a b : TangentSpace (𝓡 n) p),
        (g i).inner p a b =
          gN.inner (q i p)
            (mfderiv (𝓡 n) (𝓡 n) (q i) p a)
            (mfderiv (𝓡 n) (𝓡 n) (q i) p b) := by
  classical
  let L : forall i, P i -> (EuclideanSpace ℝ (Fin n)) ≃L[ℝ] (EuclideanSpace ℝ (Fin n)) :=
    fun i p => (hq i).mfderivToContinuousLinearEquiv (by simp) p
  let Inv : forall i, P i -> (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) :=
    fun i p => (L i p).symm.toContinuousLinearMap
  have hright (i : A) (p : P i) (a : (EuclideanSpace ℝ (Fin n))) :
      mfderiv (𝓡 n) (𝓡 n) (q i) p (Inv i p a) = a :=
    (L i p).apply_symm_apply a
  have hleft (i : A) (p : P i) (a : (EuclideanSpace ℝ (Fin n))) :
      Inv i p (mfderiv (𝓡 n) (𝓡 n) (q i) p a) = a :=
    (L i p).symm_apply_apply a
  let originalForm : forall i, P i -> (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    fun i p => (g i).inner p
  let B : forall i, P i -> (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    fun i p => (originalForm i p).bilinearComp (Inv i p) (Inv i p)
  have hB (i : A) (p : P i) (a b : (EuclideanSpace ℝ (Fin n))) :
      B i p a b = (g i).inner p (Inv i p a) (Inv i p b) := rfl
  have hcompat (i j : A) (p : P i) (p' : P j) (heq : q i p = q j p')
      (a b : (EuclideanSpace ℝ (Fin n))) : B i p a b = B j p' a b :=
    hinv i j p p' heq _ _ _ _
      ((hright i p a).trans (hright j p' a).symm)
      ((hright i p b).trans (hright j p' b).symm)
  choose idx pt hpt using hcover
  have hsymm (i : A) (p : P i) (a b : (EuclideanSpace ℝ (Fin n))) : B i p a b = B i p b a :=
    (g i).symm p _ _
  have hpos (i : A) (p : P i) (a : (EuclideanSpace ℝ (Fin n))) (ha : a ≠ 0) : 0 < B i p a a := by
    apply (g i).pos p
    intro hzero
    change Inv i p a = (0 : (EuclideanSpace ℝ (Fin n))) at hzero
    apply ha
    exact (L i p).symm.injective (by simpa [Inv] using hzero)
  let gN : RiemannianMetric n N :=
    { inner := fun y => B (idx y) (pt y)
      symm := fun y => hsymm (idx y) (pt y)
      pos := fun y => hpos (idx y) (pt y)
      isVonNBounded := by
        intro y
        let i := idx y
        let p := pt y
        have heq : {v : EuclideanSpace ℝ (Fin n) | B i p v v < 1} =
            (L i p).toContinuousLinearMap '' {v | (g i).inner p v v < 1} := by
          ext v
          constructor
          · intro hv
            exact ⟨Inv i p v, hv, hright i p v⟩
          · rintro ⟨w, hw, rfl⟩
            change originalForm i p ((L i p).symm (L i p w))
              ((L i p).symm (L i p w)) < 1
            rw [ContinuousLinearEquiv.symm_apply_apply]
            exact hw
        change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin n) | B i p v v < 1}
        rw [heq]
        exact ((g i).isVonNBounded p).image _
      contMDiff := by
        intro y
        let i := idx y
        let p := pt y
        have hqy : q i p = y := hpt y
        let s := (hq i p).localInverse
        have hs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ s (q i p) :=
          (hq i p).localInverse_contMDiffAt
        have hsec : ∀ᶠ z in 𝓝 (q i p), q i (s z) = z :=
          (hq i p).localInverse_eventuallyEq_right
        have hsmd : ∀ᶠ z in 𝓝 (q i p), MDifferentiableAt (𝓡 n) (𝓡 n) s z := by
          filter_upwards [s.open_source.mem_nhds (hq i p).localInverse_mem_source] with z hz
          exact s.mdifferentiableAt (by simp) hz
        have hkey : ∀ᶠ z in 𝓝 (q i p),
            B (idx z) (pt z) = inducedForm (I := (𝓡 n))
              (J := (𝓡 n)) (g i) s z := by
          filter_upwards [hsec, hsmd, hsec.eventually_nhds] with z hz hmd hz2
          have hDs (a : (EuclideanSpace ℝ (Fin n))) : Inv i (s z) a = mfderiv (𝓡 n) (𝓡 n) s z a := by
            apply (L i (s z)).injective
            exact (hright i (s z) a).trans
              (mfderiv_localSection_rightInverse
                hmd ((hq i).mdifferentiable (by simp) _) hz2 a).symm
          ext a b
          rw [hcompat (idx z) i (pt z) (s z) ((hpt z).trans hz.symm), hB, hDs, hDs]
          rfl
        rw [← hqy]
        refine (inducedForm_contMDiffAt (g i) hs).congr_of_eventuallyEq ?_
        filter_upwards [hkey] with z hz
        rw [hz] }
  have hpres (i : A) (p : P i) (a b : TangentSpace (𝓡 n) p) :
      (g i).inner p a b = gN.inner (q i p)
        (mfderiv (𝓡 n) (𝓡 n) (q i) p a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) p b) := by
    change _ = B (idx (q i p)) (pt (q i p)) _ _
    rw [hcompat (idx (q i p)) i (pt (q i p)) p (hpt (q i p)), hB, hleft, hleft]
  refine ⟨gN, hpres, ?_⟩
  intro gN' hgN'
  have hinn : gN'.inner = gN.inner := by
    funext y
    let i := idx y
    let p := pt y
    have hqy : q i p = y := hpt y
    rw [← hqy]
    ext a b
    obtain ⟨a', rfl⟩ := (L i p).surjective a
    obtain ⟨b', rfl⟩ := (L i p).surjective b
    exact (hgN' i p a' b').symm.trans (hpres i p a' b')
  generalize hg : gN = gN0 at *
  cases gN0
  cases gN'
  cases hinn
  rfl

end Poincare.Gluing
