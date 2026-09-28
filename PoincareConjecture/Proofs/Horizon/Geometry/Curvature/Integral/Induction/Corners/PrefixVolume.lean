import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.IteratedFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Equivalence








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

private theorem full_surjective_of_last_prefix_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}
    (F : M → Fin (k + 1) → ℝ)
    (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F) (x : M)
    (hs : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ)
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
        (F y (Fin.last k)) (fun i => F y i.castSucc)) x)) :
    Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ) F x) := by
  intro b
  obtain ⟨v, hv⟩ := hs (Fin.cons (b (Fin.last k)) (fun i => b i.castSucc))
  refine ⟨v, ?_⟩
  have hcoords := contMDiff_pi_space.mp hF
  have hj : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞
      (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
        (F y (Fin.last k)) (fun i => F y i.castSucc)) :=
    contMDiff_pi_space.mpr (Fin.cases (hcoords (Fin.last k)) (fun i => hcoords i.castSucc))
  apply funext
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h := congrFun hv 0
    simpa only [mfderiv_pi_apply _ (contMDiff_pi_space.mp hj), Fin.cons_zero,
      mfderiv_pi_apply _ hcoords] using h
  · have h := congrFun hv i.succ
    simpa only [mfderiv_pi_apply _ (contMDiff_pi_space.mp hj), Fin.cons_succ,
      mfderiv_pi_apply _ hcoords] using h

private theorem last_prefix_eq_iff {k : ℕ} (x c : Fin (k + 1) → ℝ) :
    Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (x (Fin.last k)) (fun i => x i.castSucc) =
      Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (c (Fin.last k)) (fun i => c i.castSucc) ↔ x = c := by
  constructor
  · intro h
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact congrFun h 0
    · exact congrFun h i.succ
  · rintro rfl
    rfl

end Poincare.Geometry.Manifold.RegularFiber

namespace PoincareConjecture.RiemannianMetric

private theorem pullback_inner_openFiberEquivOfEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {m k : ℕ} [Fact (Module.finrank ℝ E = m + k)]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E)))
    {f h : M → Fin k → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (hh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ h)
    (U : Opens M)
    (hregf : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (hregh : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) h x))
    {c d : Fin k → ℝ}
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ U ∧ h x = d)) :
    letI := openFiberChartedSpace (m := m) hf U hregf c
    letI := openFiberChartedSpace (m := m) hh U hregh d
    letI := isManifold_openFiber (m := m) hf U hregf c
    letI := isManifold_openFiber (m := m) hh U hregh d
    let gF := Induced.pullbackMetric g (openFiberIncl f U c)
      (contMDiff_openFiberIncl (m := m) hf U hregf c)
      (injective_mfderiv_openFiberIncl (m := m) hf U hregf c)
    let gH := Induced.pullbackMetric g (openFiberIncl h U d)
      (contMDiff_openFiberIncl (m := m) hh U hregh d)
      (injective_mfderiv_openFiberIncl (m := m) hh U hregh d)
    let e := openFiberDiffeomorphOfEq (m := m) hf hh hregf hregh he
    ∀ x v w, gF.inner x v w = gH.inner (e x)
      (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
  let := openFiberChartedSpace (m := m) hf U hregf c
  let := openFiberChartedSpace (m := m) hh U hregh d
  let := isManifold_openFiber (m := m) hf U hregf c
  let := isManifold_openFiber (m := m) hh U hregh d
  let e := openFiberDiffeomorphOfEq (m := m) hf hh hregf hregh he
  dsimp only
  intro x v w
  have hcomp := mfderiv_comp x
    ((contMDiff_openFiberIncl hh U hregh d (e x)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiable (by simp) x)
  have heq : openFiberIncl h U d ∘ e = openFiberIncl f U c := rfl
  rw [heq] at hcomp
  change g.inner (openFiberIncl f U c x)
      (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x v)
      (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) x w) =
    g.inner (openFiberIncl h U d (e x))
      (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl h U d) (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v))
      (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl h U d) (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x w))
  rw [hcomp]
  rfl

end PoincareConjecture.RiemannianMetric


theorem PoincareConjecture.RiemannianMetric.exists_prefix_fiber_volume_identity
    {d k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((d + 1) + k))) M]
    [IsManifold (𝓡 ((d + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((d + 1) + k) M)
    (f : Fin (k + 1) → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : TopologicalSpace.Opens M)
    (hprefix : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ)
        (fun y (i : Fin k) => f i.castSucc y) x)) :
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
      (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
    letI (c : Fin k → ℝ) := openFiberChartedSpace (m := d + 1) hP U hprefix c
    letI (c : Fin k → ℝ) := isManifold_openFiber (m := d + 1) hP U hprefix c
    (∀ c : Fin k → ℝ, ∀ x : openFiber P U c,
      mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ)
        (f (Fin.last k) ∘ openFiberIncl P U c) x ≠ 0) →
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hfull : ∀ x ∈ U, Function.Surjective
        (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) F x),
      ∀ c : Fin (k + 1) → ℝ,
        let cP := fun i : Fin k => c i.castSucc
        let gP := g.openRegularFiberMetric hP U hprefix cP
        let φP := f (Fin.last k) ∘ openFiberIncl P U cP
        let hφP := (hf (Fin.last k)).comp
          (contMDiff_openFiberIncl (m := d + 1) hP U hprefix cP)
        ∃ hlevel : ∀ x : openFiber P U cP,
            mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φP x ≠ 0,
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
            d + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
          letI := openFiberChartedSpace (m := d) hF U hfull c
          letI := isManifold_openFiber (m := d) hF U hfull c
          let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
            (openFiberIncl F U c)
            (contMDiff_openFiberIncl (m := d) hF U hfull c)
            (injective_mfderiv_openFiberIncl (m := d) hF U hfull c)
          ∀ A : Set M,
            (gP.regularLevelVolume hφP ⊤ (fun x _ => hlevel x) (c (Fin.last k))).real
              {z | openFiberIncl P U cP (openLevelIncl φP ⊤ (c (Fin.last k)) z) ∈ A} =
            (PoincareConjecture.RiemannianMetric.volumeMeasure gFull).real
              {y | openFiberIncl F U c y ∈ A} := by
  classical
  let P := fun y (i : Fin k) => f i.castSucc y
  let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
    (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := d + 1) hP U hprefix c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := d + 1) hP U hprefix c
  dsimp only
  intro hlast
  let F := fun y i => f i y
  have hF : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
    contMDiff_pi_space.mpr hf
  let joint := fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ)
    (f (Fin.last k) y) (P y)
  obtain ⟨hjoint, hjsmooth, hiter⟩ :=
    g.exists_iterated_openFiber_scalar_integral_equivalence hP (hf (Fin.last k))
      U hprefix hlast
  have hfull : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) F x) := by
    intro x hx
    exact full_surjective_of_last_prefix_surjective F hF x (hjoint x hx)
  refine ⟨hfull, ?_⟩
  intro c
  let cP := fun i : Fin k => c i.castSucc
  let t := c (Fin.last k)
  let gP := g.openRegularFiberMetric hP U hprefix cP
  let φP := f (Fin.last k) ∘ openFiberIncl P U cP
  let hφP := (hf (Fin.last k)).comp
    (contMDiff_openFiberIncl (m := d + 1) hP U hprefix cP)
  obtain ⟨hlevel, hdata⟩ := hiter cP t
  refine ⟨hlevel, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hφP ⊤ (fun x _ => hlevel x) d t
  let := isManifold_openLevelSet hφP ⊤ (fun x _ => hlevel x) d t
  let gIter := PoincareConjecture.RiemannianMetric.regularLevelMetric
    hφP ⊤ (fun x _ => hlevel x) t gP
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
    d + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := d) hjsmooth U hjoint (Fin.cons t cP)
  let := isManifold_openFiber (m := d) hjsmooth U hjoint (Fin.cons t cP)
  let gJoint := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
    (openFiberIncl joint U (Fin.cons t cP))
    (contMDiff_openFiberIncl (m := d) hjsmooth U hjoint (Fin.cons t cP))
    (injective_mfderiv_openFiberIncl (m := d) hjsmooth U hjoint (Fin.cons t cP))
  let := openFiberChartedSpace (m := d) hF U hfull c
  let := isManifold_openFiber (m := d) hF U hfull c
  let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
    (openFiberIncl F U c) (contMDiff_openFiberIncl (m := d) hF U hfull c)
    (injective_mfderiv_openFiberIncl (m := d) hF U hfull c)
  obtain ⟨e₁, he₁, _, _, hvol₁, _⟩ := hdata
  have heq : ∀ x, (x ∈ U ∧ joint x = Fin.cons t cP) ↔ (x ∈ U ∧ F x = c) := by
    intro x
    exact and_congr_right (fun _ => last_prefix_eq_iff (F x) c)
  let e₂ := openFiberDiffeomorphOfEq (m := d) hjsmooth hF hjoint hfull heq
  have hmetric := PoincareConjecture.RiemannianMetric.pullback_inner_openFiberEquivOfEq
    (m := d) g hjsmooth hF U hjoint hfull heq
  have hdist : ∀ x y, PoincareConjecture.RiemannianMetric.edist gFull (e₂ x) (e₂ y) =
      PoincareConjecture.RiemannianMetric.edist gJoint x y :=
    PoincareConjecture.RiemannianMetric.edist_eq_of_diffeomorph_metric_pullback gJoint gFull e₂ hmetric
  have hvol₂ := PoincareConjecture.RiemannianMetric.measurePreserving_volumeMeasure_of_edist_eq
    gJoint gFull e₂.toEquiv hdist
  have hambient (x : openLevelSet φP ⊤ t) :
      openFiberIncl F U c (e₂ (e₁ x)) =
        openFiberIncl P U cP (openLevelIncl φP ⊤ t x) := by
    change openFiberIncl joint U (Fin.cons t cP) (e₁.toEquiv x) = _
    rw [he₁]
    rfl
  intro A
  have hvol := (hvol₂.comp hvol₁).measure_preimage_emb
    (e₁.trans e₂).toHomeomorph.measurableEmbedding (openFiberIncl F U c ⁻¹' A)
  have hpre : (e₂.toEquiv ∘ e₁) ⁻¹' (openFiberIncl F U c ⁻¹' A) =
      {z | openFiberIncl P U cP (openLevelIncl φP ⊤ t z) ∈ A} := by
    ext x
    change openFiberIncl F U c (e₂ (e₁ x)) ∈ A ↔ _
    rw [hambient]
    rfl
  rw [hpre] at hvol
  exact congrArg ENNReal.toReal hvol
