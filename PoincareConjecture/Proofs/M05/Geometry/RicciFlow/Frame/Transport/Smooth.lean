
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Spatial
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.HigherRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u
noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

private def chartTransport (F : RicciFlow n M (Ico a b)) (x : M)
    (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    x ((extChartAt (𝓡 n) x).symm z) x ((extChartAt (𝓡 n) x).symm z)
    (canonicalTransport F t ((extChartAt (𝓡 n) x).symm z))

private theorem chartTransport_contDiffOn
    (F : RicciFlow n M (Ico a b)) (x : M) {c : ℝ} (hac : a ≤ c) (hcb : c < b) :
    ContDiffOn ℝ ∞ (Function.uncurry (chartTransport F x))
      ((extChartAt (𝓡 n) x).target ×ˢ Icc a c) := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace
  let e := extChartAt (𝓡 n) x
  let A : E → ℝ → (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E := fun z s =>
    ContinuousLinearMap.compL ℝ E E E (chartRicciCoefficient F x z s)
  have hsub : Icc a c ⊆ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_lt hcb⟩
  have hzbase (z : E) (hz : z ∈ e.target) : e.symm z ∈
      (trivializationAt E (TangentSpace (𝓡 n)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [e, extChartAt_source] using e.map_target hz
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) (e.target ×ˢ Icc a c) :=
    (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn
      ((chartRicciCoefficient_contDiffOn F x).mono (prod_mono Subset.rfl hsub))
  have hinit : ContDiffOn ℝ ∞ (fun z => chartTransport F x z a) e.target := by
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => ContinuousLinearMap.id ℝ E)
      e.target).congr
    intro z hz
    exact canonicalTransport_coordinates_initial F (hac.trans_lt hcb) x _ (hzbase z hz)
  have hsol : ∀ z ∈ e.target, ∀ s ∈ Icc a c,
      HasDerivWithinAt (chartTransport F x z)
        (A z s (chartTransport F x z s)) (Icc a c) s := by
    intro z hz s hs
    exact (canonicalTransport_coordinates_hasDerivWithinAt F x _ (hzbase z hz)
      (hsub hs)).mono hsub
  exact linearODE_contDiffOn A hac (isOpen_extChartAt_target x) hA
    (chartTransport F x) hinit hsol

private theorem canonicalTransport_contMDiffOn_of_chart
    (F : RicciFlow n M (Ico a b)) {m : WithTop ℕ∞}
    (hchart : ∀ x : M, ∀ c : ℝ, a ≤ c → c < b →
      ContDiffOn ℝ m (Function.uncurry (chartTransport F x))
        ((extChartAt (𝓡 n) x).target ×ˢ Icc a c)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) m
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        p.2 (canonicalTransport F p.1 p.2)) (Ico a b ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hac : a ≤ c := ht.1.trans htc.le
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let e := extChartAt (𝓡 n) x
  let S : Set (ℝ × M) := Icc a c ×ˢ e.source
  have harg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) m
      (fun p : ℝ × M => (e p.2, p.1)) S (t, x) :=
    ((contMDiffAt_extChartAt (I := 𝓡 n) (x := x)).comp (t, x)
      contMDiffAt_snd).contMDiffWithinAt.prodMk contMDiffWithinAt_fst
  have hmap : MapsTo (fun p : ℝ × M => (e p.2, p.1)) S (e.target ×ˢ Icc a c) :=
    fun p hp => ⟨e.map_source hp.2, hp.1⟩
  have h := ((hchart x c hac hcb) (e x, t)
    ⟨mem_extChartAt_target x, ht.1, htc.le⟩).contMDiffWithinAt
  have hc := h.comp (t, x) (by
    simpa +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using harg) hmap
  have hS : S ∈ 𝓝[Ico a b ×ˢ univ] (t, x) := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iio c ×ˢ e.source,
      (isOpen_Iio.prod (isOpen_extChartAt_source (I := 𝓡 n) x)).mem_nhds
        ⟨htc, mem_extChartAt_source x⟩, ?_⟩
    intro p hp
    exact ⟨⟨hp.2.1.1, hp.1.1.le⟩, hp.1.2⟩
  have hlocal := hc.mono_of_mem_nhdsWithin hS
  apply hlocal.congr_of_eventuallyEq
  · filter_upwards [hS] with p hp
    exact congrArg (fun y : M =>
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x y x y
        (canonicalTransport F p.1 y)) (e.left_inv hp.2).symm
  · exact congrArg (fun y : M =>
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x y x y
        (canonicalTransport F t y)) (e.left_inv (mem_extChartAt_source x)).symm



theorem canonicalTransport_contMDiffOn (F : RicciFlow n M (Ico a b)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        p.2 (canonicalTransport F p.1 p.2)) (Ico a b ×ˢ univ) :=
  canonicalTransport_contMDiffOn_of_chart F (fun x _ hac hcb =>
    chartTransport_contDiffOn F x hac hcb)


theorem canonicalTransport_contMDiffAt_interior (F : RicciFlow n M (Ico a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        p.2 (canonicalTransport F p.1 p.2)) (t, x) := by
  have h := (canonicalTransport_contMDiffOn F).mono
    (prod_mono (Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b) Subset.rfl)
  exact h.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)

end PoincareConjecture.RicciFlow.Frame
