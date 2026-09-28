import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.AttainmentRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorGram
import Mathlib.MeasureTheory.Measure.OpenPos










set_option autoImplicit false

open Set MeasureTheory Filter Metric Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}




structure M65InteriorDiskRepresentative (connection : LeviCivitaData g)
    (F : M65WeakDisk e γ) (f : LoopPlane → M) : Prop where
  smooth : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1)
  value_ae : f =ᵐ[volume.restrict (ball (0 : LoopPlane) 1)] F.value
  derivative_ae : ∀ i : Fin 2,
    (fun z => fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =ᵐ[
      volume.restrict (ball (0 : LoopPlane) 1)] F.derivative i
  harmonic : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension connection f z = 0




theorem m65Attainment_gram_ae (F : M65WeakDisk e γ) {f : LoopPlane → M}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hf : M65InteriorDiskRepresentative connection F f) :
    ∀ᵐ z ∂volume.restrict (ball (0 : LoopPlane) 1), ∀ i j : Fin 2,
      m60AreaGram g f z i j = m65EmbeddingMetric g e (F.value z)
        (F.derivative i z) (F.derivative j z) := by
  filter_upwards [hf.value_ae, (ae_all_iff.mpr hf.derivative_ae),
    ae_restrict_mem isOpen_ball.measurableSet] with z hvalue hderiv hz
  have hdf := (hf.smooth.contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt
    (by simp)
  have hchain (i : Fin 2) : F.derivative i z =
      mfderiv (𝓡 3) (𝓡 N) e (f z)
        (mfderiv (𝓡 2) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    rw [← hderiv i, ← mfderiv_eq_fderiv,
      mfderiv_comp z (he.mdifferentiableAt (by simp)) hdf]
    rfl
  intro i j
  rw [← hvalue, hchain i, hchain j, m65EmbeddingMetric_image g e (f z) (hinj (f z))]
  rfl




theorem m65Attainment_area_eq (F : M65WeakDisk e γ) {f : LoopPlane → M}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hf : M65InteriorDiskRepresentative connection F f) :
    parametrizedRiemannianArea g f = F.area g := by
  have hGram := m65Attainment_gram_ae F he hinj hf
  have hclosed : ∀ᵐ z ∂volume.restrict loopDiskSet, ∀ i j : Fin 2,
      m60AreaGram g f z i j = m65EmbeddingMetric g e (F.value z)
        (F.derivative i z) (F.derivative j z) := by
    filter_upwards [m65Ae_mem_openLoopDisk, ae_restrict_of_ae (ae_imp_of_ae_restrict hGram)]
      with z hz hG
    exact hG hz
  unfold parametrizedRiemannianArea M65WeakDisk.area
  apply integral_congr_ae
  filter_upwards [hclosed] with z hz
  have hsymm : m60AreaGram g f z 1 0 = m60AreaGram g f z 0 1 :=
    g.symm _ _ _
  change Real.sqrt (max 0 (m60AreaGram g f z).det) =
    Real.sqrt (m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 0 z) *
      m65EmbeddingMetric g e (F.value z) (F.derivative 1 z) (F.derivative 1 z) -
      (m65EmbeddingMetric g e (F.value z) (F.derivative 0 z) (F.derivative 1 z)) ^ 2)
  rw [max_eq_right (m65AreaGram_posSemidef g f z).det_nonneg,
    Matrix.det_fin_two, hsymm, ← pow_two, hz 0 0, hz 1 1, hz 0 1]




theorem m65Attainment_conformal (F : M65WeakDisk e γ) {f : LoopPlane → M}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hf : M65InteriorDiskRepresentative connection F f) (hconf : F.Conformal g) :
    ∀ z ∈ ball (0 : LoopPlane) 1, ∃ c : ℝ,
      m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hcol (i : Fin 2) : ContinuousOn (fun z => (⟨f z,
      mfderiv (𝓡 2) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
        TangentBundle (𝓡 3) M)) (ball (0 : LoopPlane) 1) := by
    intro z hz
    exact (RiemannianMetric.contMDiffAt_mfderiv_const_vector
      (hf.smooth.contMDiffAt (isOpen_ball.mem_nhds hz)) _).continuousAt.continuousWithinAt
  have hG (i j : Fin 2) : ContinuousOn (fun z => m60AreaGram g f z i j)
      (ball (0 : LoopPlane) 1) := (hcol i).inner_bundle (hcol j)
  have hae : ∀ᵐ z ∂volume.restrict (ball (0 : LoopPlane) 1),
      m60AreaGram g f z 0 0 = m60AreaGram g f z 1 1 ∧ m60AreaGram g f z 0 1 = 0 := by
    filter_upwards [m65Attainment_gram_ae F he hinj hf,
      ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hconf] with z hz hc
    rw [hz 0 0, hz 1 1, hz 0 1]
    exact hc
  have hdiag := Measure.eqOn_open_of_ae_eq (hae.mono fun _ h => h.1) isOpen_ball (hG 0 0) (hG 1 1)
  have hmix := Measure.eqOn_open_of_ae_eq (hae.mono fun _ h => h.2) isOpen_ball
    (hG 0 1) continuous_const.continuousOn
  intro z hz
  refine ⟨m60AreaGram g f z 0 0, ?_⟩
  have hsymm : m60AreaGram g f z 1 0 = m60AreaGram g f z 0 1 := g.symm _ _ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.smul_apply, Matrix.one_apply]
  · exact hmix hz
  · exact hsymm.trans (hmix hz)
  · exact (hdiag hz).symm

end PoincareConjecture
