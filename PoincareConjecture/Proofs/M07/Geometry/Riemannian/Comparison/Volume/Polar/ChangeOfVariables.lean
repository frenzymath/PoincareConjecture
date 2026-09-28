import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.ChangeOfVariables















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem volumeMeasure_image_eq_lintegral_in_chart
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hinj : InjOn f s) (hfs : f '' s ⊆ e.target) :
    g.volumeMeasure (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (g.pullbackVolumeDensity f x) := by
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := e.symm ∘ f
  have hFx (x) (hx : x ∈ s) : F x ∈ e.source :=
    e.map_target (hfs ⟨x, hx, rfl⟩)
  have hFd (x) (hx : x ∈ s) : DifferentiableAt ℝ F x := by
    exact mdifferentiableAt_iff_differentiableAt.mp
      (((hei.contMDiffAt (e.open_target.mem_nhds (hfs ⟨x, hx, rfl⟩))).mdifferentiableAt
        (by simp)).comp x (hf x hx))
  have hFi : InjOn F s := by
    intro x hx y hy hxy
    apply hinj hx hy
    exact e.symm.injOn (hfs ⟨x, hx, rfl⟩) (hfs ⟨y, hy, rfl⟩) hxy
  have hFm : MeasurableSet (F '' s) :=
    hs.image_of_continuousOn_injOn (fun x hx => (hFd x hx).continuousAt.continuousWithinAt) hFi
  have himage : e '' (F '' s) = f '' s := by
    rw [← image_comp]
    exact image_congr fun x hx => e.right_inv (hfs ⟨x, hx, rfl⟩)
  rw [← himage, g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei
    hFm (by rintro _ ⟨x, hx, rfl⟩; exact hFx x hx)]
  have hchange := g.lintegral_pullbackVolumeDensity_image hs
    (fun x hx => (he.contMDiffAt (e.open_source.mem_nhds (hFx x hx))).mdifferentiableAt
      (by simp)) hFd hFi (fun _ => 1)
  simp only [mul_one] at hchange
  rw [hchange]
  apply setLIntegral_congr_fun hs
  intro x hx
  have hloc : e ∘ F =ᶠ[𝓝 x] f := by
    filter_upwards [(hf x hx).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (hfs ⟨x, hx, rfl⟩))] with y hy
    exact e.right_inv hy
  simp only [pullbackVolumeDensity, hloc.mfderiv_eq]
  rw [hloc.eq_of_nhds]



theorem volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, MDifferentiableAt (𝓡 n) (𝓡 n) f x)
    (hinj : InjOn f s) :
    g.volumeMeasure (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (g.pullbackVolumeDensity f x) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let : Nonempty s := hne.to_subtype
  have hlocal (x : s) : ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (x : EuclideanSpace ℝ (Fin n)) ∈ U ∧
        f '' U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (f x)).source := by
    have hN := (hf x x.property).continuousAt.preimage_mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) (f x)).open_source.mem_nhds
        (mem_chart_source _ (f x)))
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hN
    exact ⟨U, hUopen, hxU, image_subset_iff.mpr hUsub⟩
  choose U hUopen hxU hU using hlocal
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    U hUopen (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let V : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun i => U (a i) ∩ s
  let D := disjointed V
  have hVm (i : ℕ) : MeasurableSet (V i) := (hUopen _).measurableSet.inter hs
  have hDm (i : ℕ) : MeasurableSet (D i) := MeasurableSet.disjointed hVm i
  have hDsub (i : ℕ) : D i ⊆ s := (disjointed_le V i).trans inter_subset_right
  have hcover : (⋃ i, D i) = s := by
    rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset fun _ => inter_subset_right
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ha hx)
      exact mem_iUnion.mpr ⟨i, hi, hx⟩
  have himageM (i : ℕ) : MeasurableSet (f '' D i) :=
    (hDm i).image_of_continuousOn_injOn
      (fun x hx => (hf x (hDsub i hx)).continuousAt.continuousWithinAt)
      (hinj.mono (hDsub i))
  have hdisj : Pairwise (fun i j => Disjoint (f '' D i) (f '' D j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hinj (hDsub i hx) (hDsub j hz) (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (disjoint_disjointed V hij) hx (hxz.symm ▸ hz)
  have hlocalVolume (i : ℕ) : g.volumeMeasure (f '' D i) =
      ∫⁻ x in D i, ENNReal.ofReal (g.pullbackVolumeDensity f x) := by
    apply g.volumeMeasure_image_eq_lintegral_in_chart
      (chartAt (EuclideanSpace ℝ (Fin n)) (f (a i))).symm
      (by simpa [extChartAt_target] using
        (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) (f (a i))))
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := f (a i)))
      (hDm i) (fun x hx => hf x (hDsub i hx)) (hinj.mono (hDsub i))
    exact (image_mono ((disjointed_le V i).trans inter_subset_left)).trans (hU (a i))
  calc
    g.volumeMeasure (f '' s) = ∑' i, g.volumeMeasure (f '' D i) := by
      rw [← hcover, image_iUnion, measure_iUnion hdisj himageM]
    _ = ∑' i, ∫⁻ x in D i, ENNReal.ofReal (g.pullbackVolumeDensity f x) := by
      simp_rw [hlocalVolume]
    _ = ∫⁻ x in s, ENNReal.ofReal (g.pullbackVolumeDensity f x) := by
      rw [← lintegral_iUnion hDm (disjoint_disjointed V), hcover]

end PoincareConjecture.RiemannianMetric
