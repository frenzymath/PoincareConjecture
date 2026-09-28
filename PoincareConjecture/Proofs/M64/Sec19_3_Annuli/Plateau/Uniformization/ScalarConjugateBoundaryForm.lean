import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarClosedCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalarCoverStrip_closure :
    closure scalarCoverStrip = {z : Cover | z.1 ∈ Icc (1 : ℝ) 2} := by
  have hprod : scalarCoverStrip = Ioo (1 : ℝ) 2 ×ˢ (univ : Set ℝ) := by
    ext z
    simp [scalarCoverStrip]
  rw [hprod, closure_prod_eq, closure_Ioo (by norm_num : (1 : ℝ) ≠ 2), closure_univ]
  ext z
  simp

def scalarConjugateFormOfDifferential (g : RiemannianMetric 2 Plane)
    (J : Plane → Plane →L[ℝ] ℝ) (x : Plane) : Plane →L[ℝ] ℝ :=
  M60.rotatedFlux
    (fun y => g.pullbackVolumeDensity id y * ((g.euclideanCoefficients y).inverse (J y)) 0)
    (fun y => g.pullbackVolumeDensity id y * ((g.euclideanCoefficients y).inverse (J y)) 1) x

def scalarCoverFormOfDifferential (g : RiemannianMetric 2 Plane)
    (J : Plane → Plane →L[ℝ] ℝ) (z : Cover) : Cover →L[ℝ] ℝ :=
  (scalarConjugateFormOfDifferential g J (scalarCoverMap z)).comp (fderiv ℝ scalarCoverMap z)

theorem scalarConjugateFormOfDifferential_continuousOn
    (g : RiemannianMetric 2 Plane) {J : Plane → Plane →L[ℝ] ℝ} {S : Set Plane}
    (hJ : ContinuousOn J S) : ContinuousOn (scalarConjugateFormOfDifferential g J) S := by
  have hIc : Continuous (fun x : Plane => (g.euclideanCoefficients x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hi : (g.euclideanCoefficients x).IsInvertible := by
      convert! g.inner_isInvertible x
    exact (hi.contDiffAt_map_inverse.comp x (g.contDiffAt_euclideanCoefficients x)).continuousAt
  have hZ : ContinuousOn (fun x : Plane => (g.euclideanCoefficients x).inverse (J x)) S :=
    hIc.continuousOn.clm_apply hJ
  have hrho : Continuous (g.pullbackVolumeDensity id) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x)
      contMDiffAt_id (by simpa using Function.injective_id)).1.continuousAt
  have hcoord (i : Fin 2) :
      ContinuousOn (fun x : Plane => ((g.euclideanCoefficients x).inverse (J x)) i) S :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn hZ
  exact ((hrho.continuousOn.mul (hcoord 1)).neg.smul continuousOn_const).add
    ((hrho.continuousOn.mul (hcoord 0)).smul continuousOn_const)

theorem scalarCoverFormOfDifferential_periodic (g : RiemannianMetric 2 Plane)
    (J : Plane → Plane →L[ℝ] ℝ) (z : Cover) :
    scalarCoverFormOfDifferential g J (z + (0, 1)) = scalarCoverFormOfDifferential g J z := by
  have heq : (fun y : Cover => scalarCoverMap (y + (0, 1))) = scalarCoverMap :=
    funext scalarCoverMap_periodic
  have hd := ((scalarCoverMap_smooth.differentiable (by simp) (z + (0, 1))).hasFDerivAt.comp
    z ((hasFDerivAt_id z).add_const (0, 1))).fderiv
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, heq] at hd
  simp only [scalarCoverFormOfDifferential, scalarCoverMap_periodic, ← hd]

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarConjugateFormOfDifferential_eq
    {H : Plane → ℝ} {J : Plane → Plane →L[ℝ] ℝ} {x : Plane}
    (hJ : J x = fderiv ℝ H x) :
    scalarConjugateFormOfDifferential g J x = scalarConjugateForm D H x := by
  have hgrad : D.gradient H x = (g.euclideanCoefficients x).inverse (J x) := by
    change (g.euclideanCoefficients x).inverse (mvfderiv (𝓡 2) H x) = _
    rw [hJ]
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  simp only [scalarConjugateFormOfDifferential, scalarConjugateForm, M60.rotatedFlux,
    scalarMetricFlux, hgrad]

theorem exists_scalarCoverForm_boundary_extension
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∃ J : Plane → Plane →L[ℝ] ℝ,
      ContinuousOn J (closure scalarAnnulus) ∧ EqOn J (fderiv ℝ H) scalarAnnulus ∧
      (∀ x ∈ closure scalarAnnulus, x ∉ scalarAnnulus → J x ≠ 0) ∧
      ContinuousOn (scalarCoverFormOfDifferential g J) (closure scalarCoverStrip) ∧
      EqOn (scalarCoverFormOfDifferential g J) (scalarCoverForm D H) scalarCoverStrip := by
  obtain ⟨J, hJc, hJeq, hJn⟩ :=
    annular_harmonic_differential_extension D hHc hHs hlap hinner houter
  have hmaps : MapsTo scalarCoverMap (closure scalarCoverStrip) (closure scalarAnnulus) :=
    (show MapsTo scalarCoverMap scalarCoverStrip scalarAnnulus from
      fun _ hz => scalarCoverMap_mem hz).closure_of_continuousOn
        scalarCoverMap_smooth.continuous.continuousOn
  have hBc : ContinuousOn (scalarCoverFormOfDifferential g J) (closure scalarCoverStrip) :=
    ((scalarConjugateFormOfDifferential_continuousOn g hJc).comp
      scalarCoverMap_smooth.continuous.continuousOn hmaps).clm_comp
        (scalarCoverMap_smooth.continuous_fderiv (by simp)).continuousOn
  refine ⟨J, hJc, hJeq, hJn, hBc, ?_⟩
  intro z hz
  unfold scalarCoverFormOfDifferential scalarCoverForm
  rw [scalarConjugateFormOfDifferential_eq D (hJeq (scalarCoverMap_mem hz))]

end PoincareConjecture.M64Uniformization
