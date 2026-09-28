import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamWeakExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusCircleTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMapCircleGreen













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "mu" => volume.restrict S
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)



theorem M64ObservedWeakAnnulus.seam_polar_column_tangent
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    ∀ᵐ p ∂mu,
      m64MorreyPolarAngularColumn a rho
        (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)) p ∈
      range (mfderiv (𝓡 n) (𝓡 m) e
        (m64AnnulusSeamExtend A.map (m64MorreyPolarStrip a rho p))) := by
  have ht (i : Fin 2) := m64MorreyPolarStrip_ae a hrho
    (ae_restrict_of_ae_restrict_of_subset hKO (A.seam_extension_tangent i))
  filter_upwards [ht 0, ht 1] with p hp0 hp1
  obtain ⟨v0, hv0⟩ := hp0
  obtain ⟨v1, hv1⟩ := hp1
  let w := fderiv ℝ (m64MorreyPolarStrip a rho) p (EuclideanSpace.single (0 : Fin 2) 1)
  refine ⟨w 0 • v0 + w 1 • v1, ?_⟩
  rw [map_add, map_smul, map_smul, hv0, hv1]
  rfl



theorem M64ObservedWeakAnnulus.seam_local_circle_traces
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (hei : IsClosedEmbedding e)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      let v := fun x => m64MorreyPolarAngularColumn a rho
        (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)) (annulusPoint x s)
      ∃ (gamma : ℝ → M) (w : ℕ → ℝ → E),
        Continuous gamma ∧ Function.Periodic gamma curvePeriod ∧
        gamma =ᵐ[circleMu] (fun x =>
          m64AnnulusSeamExtend A.map (m64MorreyPolarStrip a rho (annulusPoint x s))) ∧
        MemLp v 2 circleMu ∧
        (∀ x ∈ Icc (0 : ℝ) curvePeriod, e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) ∧
        (∀ᵐ x ∂circleMu, v x ∈ range (mfderiv (𝓡 n) (𝓡 m) e (gamma x))) ∧
        (∀ j, ContDiff ℝ 1 (w j)) ∧ (∀ j, Function.Periodic (w j) curvePeriod) ∧
        TendstoUniformlyOn w (e ∘ gamma) atTop (Icc (0 : ℝ) curvePeriod) ∧
        Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
          ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0) := by
  classical
  let F := m64AnnulusSeamExtend A.map
  let V := fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)
  let P := m64MorreyPolarStrip a rho
  let Z := m64MorreyPolarAngularColumn a rho V
  obtain ⟨hu, hv, f, hf, hperiod, hval, hder⟩ := m64WeakMap_polar_strong_approximation
    m64AnnulusSeamDomain_isOpen a hrho hKO (e ∘ F) V A.seam_extension_memLp.1
      A.seam_extension_memLp.2 A.seam_extension_weak_partial
  have hslices := m64Annulus_h1_slices_of_strong_approximation f
    (fun j => (hf j).of_le (by simp)) hperiod (fun p => e (F (P p))) Z hu hv hval hder
  have hprod := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae
    (A.seam_polar_column_tangent a hrho hKO)
  have htslices : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ∀ᵐ x ∂circleMu,
      Z (annulusPoint x s) ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F (P (annulusPoint x s)))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod)
  filter_upwards [hslices, htslices] with s hs hts
  obtain ⟨hvs, k, W, _, hW, hends, hWu, huni, hds⟩ := hs
  obtain ⟨hds, hFTC⟩ := hds
  have hT : 0 < curvePeriod := by unfold curvePeriod; positivity
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) curvePeriod := ⟨le_rfl, hT.le⟩
  have hlast : curvePeriod ∈ Icc (0 : ℝ) curvePeriod := ⟨hT.le, le_rfl⟩
  have hWr : MapsTo W (Icc (0 : ℝ) curvePeriod) (range e) :=
    m64Curve_closed_target_of_ae W hT hW hei.isClosed_range
      ⟨e (F 0), mem_range_self _⟩ (hWu.mono (fun x hx => hx ▸ mem_range_self _))
  let g0 : ℝ → M := fun x => if h : W x ∈ range e then Classical.choose h else F 0
  have hg0 (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) : e (g0 x) = W x := by
    simp only [g0, dif_pos (hWr hx)]
    exact Classical.choose_spec (hWr hx)
  have hg0c : ContinuousOn g0 (Icc (0 : ℝ) curvePeriod) :=
    hei.isEmbedding.continuousOn_iff.mpr (hW.congr hg0)
  have hgends : g0 0 = g0 curvePeriod := by
    apply hei.isEmbedding.injective
    rw [hg0 0 h0, hg0 curvePeriod hlast, hends]
  obtain ⟨gamma, hgamma, hgammaP, hgammaEq⟩ :=
    m64Curve_periodic_extension g0 hT hg0c hgends
  have hegamma (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) : e (gamma x) = W x :=
    (congrArg e (hgammaEq hx)).trans (hg0 x hx)
  have hgammaAE : gamma =ᵐ[circleMu] (fun x => F (P (annulusPoint x s))) := by
    filter_upwards [hWu, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact hei.isEmbedding.injective ((hegamma x hxI).trans hx)
  let w := fun j x => f (k j) (annulusPoint x s)
  have hpoint : ContDiff ℝ 1 (fun x => annulusPoint x s) := by
    have heq : (fun x => annulusPoint x s) = (fun x => annulusPoint 0 s +
        x • EuclideanSpace.single (0 : Fin 2) 1) := by
      funext x
      ext i
      fin_cases i <;> simp [annulusPoint]
    rw [heq]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hwc (j : ℕ) : ContDiff ℝ 1 (w j) := ((hf (k j)).of_le (by simp)).comp hpoint
  have hdw (j : ℕ) (x : ℝ) : deriv (w j) x =
      fderiv ℝ (f (k j)) (annulusPoint x s) (EuclideanSpace.single (0 : Fin 2) 1) :=
    (((hf (k j)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
      (m64AnnulusPoint_horizontal_hasDerivAt s x)).deriv
  refine ⟨gamma, w, hgamma, hgammaP, hgammaAE, hvs, ?_, ?_, hwc, ?_, ?_, ?_⟩
  · intro x hx
    rw [hegamma x hx, hegamma 0 h0]
    exact hFTC x hx
  · filter_upwards [hts, hgammaAE] with x hx hxe
    rw [hxe]
    exact hx
  · intro j x
    exact hperiod (k j) x s
  · intro U hU
    filter_upwards [huni U hU] with j hj
    intro x hx
    change (e (gamma x), w j x) ∈ U
    rw [hegamma x hx]
    exact hj x hx
  · simpa only [hdw] using hds



theorem M64ObservedWeakAnnulus.seam_local_circle_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      let r := rho * Real.exp (-s)
      ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
        (∫ p in Metric.closedBall a r,
          phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
          (∫ p in Metric.closedBall a r,
            fderiv ℝ phi p (EuclideanSpace.single i 1) • e (m64AnnulusSeamExtend A.map p)) =
          r • ∫ x in Icc (0 : ℝ) curvePeriod,
            angularPoint (x - Real.pi) i •
              (phi (a + r • angularPoint (x - Real.pi)) •
                e (m64AnnulusSeamExtend A.map (a + r • angularPoint (x - Real.pi)))) :=
  m64WeakMap_local_circle_green m64AnnulusSeamDomain_isOpen a hrho hKO
    (e ∘ m64AnnulusSeamExtend A.map)
    (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E))
    A.seam_extension_memLp.1 A.seam_extension_memLp.2 A.seam_extension_weak_partial

end PoincareConjecture
