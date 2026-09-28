import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusEnergyDensity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64MovingAnnulusCurrent_along_slice_hasDerivAt
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    (i : Fin 2) {t : ℝ} {ell : ℝ → LoopPlane} {J : Set ℝ} (hJ : IsOpen J)
    (hmap : ∀ r ∈ J, (t, ell r) ∈ O)
    (hd : ∀ r ∈ J, HasDerivAt ell (EuclideanSpace.basisFun (Fin 2) ℝ i) r)
    {x : ℝ} (hx : x ∈ J) :
    HasDerivAt
      (fun r => g.inner (v (t, ell r)) (curveVelocity (fun q => v (q, ell r)) t)
        (curveVelocity (fun q => v (t, ell q)) r))
      (fderiv ℝ (fun p => m64MovingAnnulusCurrent g v i (t, p)) (ell x)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) x := by
  have hcur : ContDiffAt ℝ ∞ (fun p => m64MovingAnnulusCurrent g v i (t, p)) (ell x) :=
    (m64MovingAnnulusCurrent_contDiffAt g
      (hv.contMDiffAt (hO.mem_nhds (hmap x hx))) i).comp (ell x)
        (contDiffAt_const.prodMk contDiffAt_id)
  have h := (hcur.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x (hd x hx)
  apply h.congr_of_eventuallyEq
  filter_upwards [hJ.mem_nhds hx] with r hr
  have hvmd := (hv.contMDiffAt (hO.mem_nhds (hmap r hr))).mdifferentiableAt (by simp)
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ × LoopPlane)
      (fun p : LoopPlane => (t, p)) (ell r) :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (ell r)).differentiableAt.mdifferentiableAt
  have hf : MDifferentiableAt (𝓡 2) (𝓡 n) (fun p => v (t, p)) (ell r) := hvmd.comp (ell r) hi
  have hell : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) ell r :=
    (hd r hr).differentiableAt.mdifferentiableAt
  have hdel : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ell r 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
    rw [mfderiv_eq_fderiv, (hd r hr).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hchain := mfderiv_comp_apply r hf hell (1 : ℝ)
  rw [hdel] at hchain
  have hvel : curveVelocity (fun q => v (t, ell q)) r =
      mfderiv (𝓡 2) (𝓡 n) (fun p => v (t, p)) (ell r)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := hchain
  rw [hvel]
  exact (m64MovingAnnulusCurrent_eq_pairing g hvmd i).symm

variable [T2Space M] [CompactSpace M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64MovingAnnulus_energyDensity_eq_current_divergence
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {v : ℝ × LoopPlane → M} {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    (hbase : ∀ p, v (0, p) = A.map p)
    {x s : ℝ} (hp : (0, annulusPoint x s) ∈ O)
    (hinside : annulusPoint x s ∈ m64AnnulusInterior) :
    deriv (fun r => m60EnergyDensity g (fun p => v (r, p)) (annulusPoint x s)) 0 =
      fderiv ℝ (fun p => m64MovingAnnulusCurrent g v 0 (0, p)) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      fderiv ℝ (fun p => m64MovingAnnulusCurrent g v 1 (0, p)) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) := by
  have hline0 : Continuous (fun y : ℝ => ((0 : ℝ), annulusPoint y s)) := by
    apply Continuous.prodMk continuous_const
    unfold annulusPoint
    fun_prop
  have hline1 : Continuous (fun r : ℝ => ((0 : ℝ), annulusPoint x r)) := by
    apply Continuous.prodMk continuous_const
    unfold annulusPoint
    fun_prop
  have h0 := m64MovingAnnulusCurrent_along_slice_hasDerivAt g hO hv 0
    (hO.preimage hline0) (fun _ hr => hr)
    (fun r _ => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_horizontal_hasDerivAt s r) hp
  have h1 := m64MovingAnnulusCurrent_along_slice_hasDerivAt g hO hv 1
    (hO.preimage hline1) (fun _ hr => hr)
    (fun r _ => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_vertical_hasDerivAt x r) hp
  have hdiv := m64MovingAnnulus_energyDensity_divergence_of_conformal_minimum
    D A hminimum hconformal hA hO hv hbase hp hinside
  rw [h0.deriv, h1.deriv] at hdiv
  simpa only [EuclideanSpace.basisFun_apply] using hdiv

end PoincareConjecture
