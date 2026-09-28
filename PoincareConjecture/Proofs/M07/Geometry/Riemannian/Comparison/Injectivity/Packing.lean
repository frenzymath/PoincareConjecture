import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.ChangeOfVariables
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
















noncomputable section
set_option autoImplicit false

open Set Filter Function MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture



theorem exists_measurable_injOn_partition
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {f : X → Y} {U : Set X}
    (hU : MeasurableSet U)
    (hlocal : ∀ x ∈ U, ∃ V ∈ 𝓝 x, InjOn f V) :
    ∃ P : ℕ → Set X, (∀ i, MeasurableSet (P i)) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = U ∧ (∀ i, InjOn f (P i)) := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => ∅, by simp, by simp [Pairwise], by simp, by simp⟩
  let : Nonempty U := hne.to_subtype
  have hopen (x : U) : ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧ InjOn f V := by
    obtain ⟨W, hW, hi⟩ := hlocal x x.property
    obtain ⟨V, hVW, hVo, hxV⟩ := mem_nhds_iff.mp hW
    exact ⟨V, hVo, hxV, hi.mono hVW⟩
  choose V hVo hxV hVi using hopen
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    V hVo (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let W : ℕ → Set X := fun i => V (a i) ∩ U
  have hWm (i : ℕ) : MeasurableSet (W i) := (hVo _).measurableSet.inter hU
  refine ⟨disjointed W, MeasurableSet.disjointed hWm, disjoint_disjointed W, ?_, ?_⟩
  · rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset fun _ => inter_subset_right
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ha hx)
      exact mem_iUnion.mpr ⟨i, hi, hx⟩
  · intro i
    exact (hVi (a i)).mono ((disjointed_le W i).trans inter_subset_left)


theorem finite_fiber_le_tsum_image_indicator
    {X Y : Type*} {f : X → Y} {U : Set X} (P : ℕ → Set X)
    (hcover : U ⊆ ⋃ i, P i) (hinj : ∀ i, InjOn f (P i))
    {k : ℕ} {q : Y} (y : Fin k → X) (hy : Injective y)
    (hfy : ∀ m, y m ∈ U ∧ f (y m) = q) :
    (k : ℝ≥0∞) ≤ ∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) q := by
  classical
  have hpiece : ∀ m, ∃ i, y m ∈ P i := fun m =>
    mem_iUnion.mp (hcover (hfy m).1)
  choose j hj using hpiece
  have hji : Injective j := by
    intro a b hab
    apply hy
    exact hinj (j a) (hj a) (hab ▸ hj b) ((hfy a).2.trans (hfy b).2.symm)
  have hm : ∀ m, (f '' P (j m)).indicator (fun _ => (1 : ℝ≥0∞)) q = 1 := by
    intro m
    rw [indicator_of_mem (show q ∈ f '' P (j m) from ⟨y m, hj m, (hfy m).2⟩)]
  calc
    (k : ℝ≥0∞) = ∑' m : Fin k,
        (f '' P (j m)).indicator (fun _ => (1 : ℝ≥0∞)) q := by
      simp only [hm, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    _ ≤ ∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) q :=
      ENNReal.tsum_comp_le_tsum_of_injective hji _



theorem mul_measure_le_tsum_injective_image
    {X Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {f : X → Y} {U : Set X} {S : Set Y} (hS : MeasurableSet S)
    (P : ℕ → Set X) (hcover : U ⊆ ⋃ i, P i)
    (hinj : ∀ i, InjOn f (P i)) (himage : ∀ i, MeasurableSet (f '' P i))
    {k : ℕ} (hpreimage : ∀ q ∈ S, ∃ y : Fin k → X,
      Injective y ∧ ∀ m, y m ∈ U ∧ f (y m) = q) :
    (k : ℝ≥0∞) * ν S ≤ ∑' i, ν (f '' P i) := by
  classical
  calc
    (k : ℝ≥0∞) * ν S = ∫⁻ q, S.indicator (fun _ => (k : ℝ≥0∞)) q ∂ν :=
      (lintegral_indicator_const hS _).symm
    _ ≤ ∫⁻ q, ∑' i, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) q ∂ν := by
      apply lintegral_mono
      intro q
      by_cases hq : q ∈ S
      · rw [indicator_of_mem hq]
        obtain ⟨y, hy, hfy⟩ := hpreimage q hq
        exact finite_fiber_le_tsum_image_indicator P hcover hinj y hy hfy
      · rw [indicator_of_notMem hq]
        exact zero_le
    _ = ∑' i, ∫⁻ q, (f '' P i).indicator (fun _ => (1 : ℝ≥0∞)) q ∂ν :=
      lintegral_tsum (fun i => (measurable_const.indicator (himage i)).aemeasurable)
    _ = ∑' i, ν (f '' P i) := by
      apply tsum_congr
      intro i
      simp only [lintegral_indicator_const (himage i), one_mul]

namespace RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem mul_volumeMeasure_le_lintegral_pullback_of_finite_fibers
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} {S : Set M}
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (he : ∀ x ∈ U, MDifferentiableAt (𝓡 n) (𝓡 n) e x)
    (hlocal : ∀ x ∈ U, ∃ V ∈ 𝓝 x, InjOn e V)
    {k : ℕ} (hpreimage : ∀ q ∈ S, ∃ y : Fin k → EuclideanSpace ℝ (Fin n),
      Injective y ∧ ∀ m, y m ∈ U ∧ e (y m) = q) :
    (k : ℝ≥0∞) * g.volumeMeasure S ≤
      ∫⁻ x in U, ENNReal.ofReal (g.pullbackVolumeDensity e x) := by
  obtain ⟨P, hP, hdisj, hcover, hinj⟩ := exists_measurable_injOn_partition hU hlocal
  have hPU (i : ℕ) : P i ⊆ U := by
    rw [← hcover]
    exact subset_iUnion P i
  have himage (i : ℕ) : MeasurableSet (e '' P i) :=
    (hP i).image_of_continuousOn_injOn
      (fun x hx => (he x (hPU i hx)).continuousAt.continuousWithinAt) (hinj i)
  calc
    (k : ℝ≥0∞) * g.volumeMeasure S ≤ ∑' i, g.volumeMeasure (e '' P i) :=
      mul_measure_le_tsum_injective_image _ hS P hcover.ge hinj himage hpreimage
    _ = ∑' i, ∫⁻ x in P i, ENNReal.ofReal (g.pullbackVolumeDensity e x) := by
      exact tsum_congr fun i =>
        g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn
          (hP i) (fun x hx => he x (hPU i hx)) (hinj i)
    _ = ∫⁻ x in U, ENNReal.ofReal (g.pullbackVolumeDensity e x) := by
      rw [← lintegral_iUnion hP hdisj, hcover]



theorem mul_volumeMeasure_le_density_bound_of_finite_fibers
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} {S : Set M} {C : ℝ}
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (he : ∀ x ∈ U, MDifferentiableAt (𝓡 n) (𝓡 n) e x)
    (hlocal : ∀ x ∈ U, ∃ V ∈ 𝓝 x, InjOn e V)
    (hC : ∀ x ∈ U, g.pullbackVolumeDensity e x ≤ C)
    {k : ℕ} (hpreimage : ∀ q ∈ S, ∃ y : Fin k → EuclideanSpace ℝ (Fin n),
      Injective y ∧ ∀ m, y m ∈ U ∧ e (y m) = q) :
    (k : ℝ≥0∞) * g.volumeMeasure S ≤ ENNReal.ofReal C * volume U := by
  refine (g.mul_volumeMeasure_le_lintegral_pullback_of_finite_fibers
    hU hS he hlocal hpreimage).trans ?_
  calc
    (∫⁻ x in U, ENNReal.ofReal (g.pullbackVolumeDensity e x)) ≤
        ∫⁻ _ in U, ENNReal.ofReal C :=
      setLIntegral_mono' hU fun x hx => ENNReal.ofReal_le_ofReal (hC x hx)
    _ = ENNReal.ofReal C * volume U := by simp

end RiemannianMetric
end PoincareConjecture
