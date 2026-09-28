import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients









set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35

open RiemannianMetric

private theorem contDiffOn_affine_time
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : ℝ × E → F} {J I : Set ℝ} {U : Set E}
    (hB : ∀ x ∈ U, ∀ t ∈ J, ContDiffWithinAt ℝ ∞ B (J ×ˢ univ) (t, x))
    (a Q : ℝ) (htime : MapsTo (fun s : ℝ => a + s / Q) I J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => Q • B (a + p.1 / Q, p.2)) (I ×ˢ U) := by
  intro p hp
  have hclock : ContDiffAt ℝ ∞ (fun z : ℝ × E => (a + z.1 / Q, z.2)) p :=
    (contDiffAt_const.add (contDiffAt_fst.div_const Q)).prodMk contDiffAt_snd
  have hmaps : MapsTo (fun z : ℝ × E => (a + z.1 / Q, z.2))
      (I ×ˢ U) (J ×ˢ univ) := fun _ hz => ⟨htime hz.1, mem_univ _⟩
  exact ((hB p.2 hp.2 _ (htime hp.1)).comp p hclock.contDiffWithinAt hmaps).const_smul Q




theorem metricFamily_contDiffWithinAt_spacetime_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) {t : ℝ} (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ univ) (t, x) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  have hid : ContMDiffWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2)) (J ×ˢ univ) (t, x) :=
    contDiffWithinAt_fst.contMDiffWithinAt.prodMk contDiffWithinAt_snd.contMDiffWithinAt
  convert! (hc.comp (t, x) hid (fun _ hp => hp)).contDiffWithinAt using 1
  funext p
  exact (constant_chart_bilinear_coordinates (n := n)
    (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl) x p.2
    ((g p.1).pullbackCoefficients f p.2)).symm




theorem metricFamily_contDiffOn_rescaled_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J I : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (a Q : ℝ) (htime : MapsTo (fun s : ℝ => a + s / Q) I J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      Q • (g (a + p.1 / Q)).pullbackCoefficients f p.2) (I ×ˢ U) := by
  exact contDiffOn_affine_time (fun x hx _ ht =>
    metricFamily_contDiffWithinAt_spacetime_pullbackCoefficients hg (hf x hx) ht) a Q htime



theorem metricFamily_contDiffOn_spacetime_chartCoefficient
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) (q : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g p.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm p.2
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
      (J ×ˢ (extChartAt (𝓡 n) q).target) := by
  intro p hp
  have hc := metricFamily_contDiffWithinAt_spacetime_pullbackCoefficients hg
    ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hp.2)) hp.1
  have hfirst := hc.clm_apply
    (contDiffWithinAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ i))
  have hsecond := hfirst.clm_apply
    (contDiffWithinAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ j))
  exact hsecond.mono (fun _ hz => ⟨hz.1, mem_univ _⟩)

end PoincareConjecture.M35
