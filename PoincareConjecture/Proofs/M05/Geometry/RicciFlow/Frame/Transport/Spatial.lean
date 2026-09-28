
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Coordinates
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Regularity
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.RicciEndomorphism.Regularity









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


def ricciCoordinate (F : RicciFlow n M (Ico a b)) (x : M) (p : ℝ × M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x p.2 x p.2
    (ricciEndomorphism F p.2 p.1)

theorem contMDiffWithinAt_ricciCoordinate (F : RicciFlow n M (Ico a b)) (x y : M)
    {t : ℝ} (ht : t ∈ Ico a b)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (ricciCoordinate F x) (Ico a b ×ˢ univ) (t, y) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z) x
  have he : TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (E := fun z => TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z)
      y (ricciEndomorphism F y t) ∈ e.source := by
    simpa [e] using hy
  have h := (e.contMDiffWithinAt_iff
    (f := fun p : ℝ × M => TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (E := fun z => TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z)
      p.2 (ricciEndomorphism F p.2 p.1)) (x₀ := (t, y)) he).mp
    (contMDiffOn_ricciEndomorphism F (t, y) ⟨ht, mem_univ y⟩) |>.2
  simp only [e, hom_trivializationAt_apply] at h
  convert h using 1 <;> rfl


def chartRicciCoefficient (F : RicciFlow n M (Ico a b)) (x : M)
    (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ricciCoordinate F x (t, (extChartAt (𝓡 n) x).symm z)

theorem chartRicciCoefficient_contDiffOn (F : RicciFlow n M (Ico a b)) (x : M) :
    ContDiffOn ℝ ∞ (Function.uncurry (chartRicciCoefficient F x))
      ((extChartAt (𝓡 n) x).target ×ˢ Ico a b) := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  have hz' : (extChartAt (𝓡 n) x).symm z ∈
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz
  have harg : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.2, (extChartAt (𝓡 n) x).symm p.1))
      ((extChartAt (𝓡 n) x).target ×ˢ Ico a b) (z, t) :=
    contMDiffWithinAt_snd.prodMk
      (((contMDiffOn_extChartAt_symm x) z hz).comp (z, t) contMDiffWithinAt_fst mapsTo_fst_prod)
  have h := (contMDiffWithinAt_ricciCoordinate F x _ ht hz').comp (z, t) harg
    (show MapsTo (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (p.2, (extChartAt (𝓡 n) x).symm p.1))
      ((extChartAt (𝓡 n) x).target ×ˢ Ico a b) (Ico a b ×ˢ univ) from
      fun p hp => ⟨hp.2, mem_univ _⟩)
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffWithinAt

private theorem canonicalTransport_chart_contDiffOn
    (F : RicciFlow n M (Ico a b)) (x : M) {t : ℝ} (ht : t ∈ Ico a b) :
    ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) =>
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        x ((extChartAt (𝓡 n) x).symm z) x ((extChartAt (𝓡 n) x).symm z)
        (canonicalTransport F t ((extChartAt (𝓡 n) x).symm z)))
      (extChartAt (𝓡 n) x).target := by
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
  let Φ : E → ℝ → E →L[ℝ] E := fun z s =>
    ContinuousLinearMap.inCoordinates E (TangentSpace (𝓡 n)) E (TangentSpace (𝓡 n))
      x (e.symm z) x (e.symm z) (canonicalTransport F s (e.symm z))
  have hsub : Icc a t ⊆ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hzbase (z : E) (hz : z ∈ e.target) : e.symm z ∈
      (trivializationAt E (TangentSpace (𝓡 n)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [e, extChartAt_source] using e.map_target hz
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) (e.target ×ˢ Icc a t) :=
    (ContinuousLinearMap.compL ℝ E E E).contDiff.comp_contDiffOn
      ((chartRicciCoefficient_contDiffOn F x).mono (prod_mono Subset.rfl hsub))
  have hinit : ContDiffOn ℝ ∞ (fun z => Φ z a) e.target := by
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => ContinuousLinearMap.id ℝ E)
      e.target).congr
    intro z hz
    exact canonicalTransport_coordinates_initial F (ht.1.trans_lt ht.2) x _ (hzbase z hz)
  have hsol : ∀ z ∈ e.target, ∀ s ∈ Icc a t,
      HasDerivWithinAt (Φ z) (A z s (Φ z s)) (Icc a t) s := by
    intro z hz s hs
    exact (canonicalTransport_coordinates_hasDerivWithinAt F x _ (hzbase z hz)
      (hsub hs)).mono hsub
  exact linearODE_contDiffOn_spatial A ht.1 (isOpen_extChartAt_target x) hA Φ hinit hsol
    (right_mem_Icc.mpr ht.1)



theorem canonicalTransport_contMDiff_spatial (F : RicciFlow n M (Ico a b))
    {t : ℝ} (ht : t ∈ Ico a b) :
    ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        x (canonicalTransport F t x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have h := (canonicalTransport_chart_contDiffOn F x ht).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hc := h.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓡 n) (x := x))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓡 n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact congrArg (fun z : M =>
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x z x z
      (canonicalTransport F t z)) ((extChartAt (𝓡 n) x).left_inv hy).symm

end PoincareConjecture.RicciFlow.Frame
