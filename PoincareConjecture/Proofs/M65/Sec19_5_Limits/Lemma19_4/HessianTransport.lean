import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneHessian










set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




theorem planeHessian_chart
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (p : M)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U) {x : LoopPlane} (hx : x ∈ U)
    (hsource : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hmetric : ∀ᶠ y in 𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)),
      ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner y a b = g.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y a)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y b))
    (u v : LoopPlane) :
    m65PlaneHessian D f x u v =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x))
        (covariantHessianMap DE ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) x u v) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  let G := c ∘ f
  let W := U ∩ f ⁻¹' c.source
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxW : x ∈ W := ⟨hx, hsource⟩
  have hG : ContDiffOn ℝ ∞ G W :=
    (contMDiffOn_chart.comp (hf.mono inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  have hGx : ContDiffAt ℝ ∞ G x := (hG x hxW).contDiffAt (hW.mem_nhds hxW)
  have hfx : MDifferentiableAt (𝓡 2) (𝓡 n) f x :=
    ((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  let line : ℝ → LoopPlane := fun r => x + r • u
  let Ω := line ⁻¹' W
  let C : LoopPlane → EuclideanSpace ℝ (Fin n) := fun y => fderiv ℝ G y v
  let k : ℝ → EuclideanSpace ℝ (Fin n) := C ∘ line
  have hline : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hline0 : line 0 = x := by simp [line]
  have hΩ : IsOpen Ω := hW.preimage hline.continuous
  have h0 : (0 : ℝ) ∈ Ω := by simpa only [Ω, mem_preimage, hline0] using hxW
  have hC : ContDiffOn ℝ ∞ C W :=
    (hG.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have hk : ContDiffOn ℝ ∞ k Ω := hC.comp hline.contDiffOn (fun _ hr => hr)
  have hlineD : HasDerivAt line u 0 := by
    simpa +instances only [line, zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const u)
  have hC0 : DifferentiableAt ℝ C (line 0) := by
    rw [hline0]
    exact ((hC x hxW).contDiffAt (hW.mem_nhds hxW)).differentiableAt (by simp)
  have hkderiv : deriv k 0 = fderiv ℝ C x u := by
    simpa +instances only [k, hline0] using! (hC0.hasFDerivAt.comp_hasDerivAt 0 hlineD).deriv
  have hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (fun r => f (line r)) 0 := by
    have hf0 : MDifferentiableAt (𝓡 2) (𝓡 n) f (line 0) := hline0.symm ▸ hfx
    exact hf0.comp 0 hlineD.differentiableAt.mdifferentiableAt
  have hfields : (fun r => mfderiv (𝓡 2) (𝓡 n) f (line r) v) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => chartVectorField p (k r) (f (line r))) := by
    filter_upwards [hΩ.mem_nhds h0] with r hr
    exact (m65PlaneDerivative_chart p
      (((hf (line r) hr.1).contMDiffAt (hU.mem_nhds hr.1)).mdifferentiableAt (by simp))
      hr.2 v).symm
  have hsource0 : f (line 0) ∈ c.source := by simpa only [hline0] using hsource
  have hpull := M62.pullback_chart_field D p hγ hsource0 hΩ h0 k hk
  have hk0 : k 0 = fderiv ℝ G x v := by simp only [k, C, Function.comp_apply, hline0]
  have hvelocity : curveVelocity (fun r => f (line r)) 0 = mfderiv (𝓡 2) (𝓡 n) f x u :=
    m65CurveVelocity_affineLine hfx u
  have hramp : m65PlaneHessian D f x u v = chartVectorField p (deriv k 0) (f x) +
      D.connection (chartVectorField p (fderiv ℝ G x v)) (f x)
        (mfderiv (𝓡 2) (𝓡 n) f x u) := by
    exact (M62.pullback_congr D hfields).trans (by
      rw [hline0, hk0, hvelocity] at hpull
      exact hpull)
  have hcinv : (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)) = f x := c.left_inv hsource
  have hpush (a : EuclideanSpace ℝ (Fin n)) : chartVectorField p a (f x) =
      mfderiv (𝓡 n) (𝓡 n) c.symm (G x) a := by
    have ht := chartVectorField_at_inverse p a (c (f x)) (c.map_source hsource)
    rw [hcinv] at ht
    exact ht
  have hdf : mfderiv (𝓡 2) (𝓡 n) f x u =
      mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (fderiv ℝ G x u) :=
    (m65PlaneDerivative_chart p hfx hsource u).symm.trans (hpush _)
  have hconn : D.connection (chartVectorField p (fderiv ℝ G x v)) (f x)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (G x) (fderiv ℝ G x u)) =
      mfderiv (𝓡 n) (𝓡 n) c.symm (G x)
        (connectionCoefficient DE (G x) (fderiv ℝ G x u) (fderiv ℝ G x v)) := by
    have ht := connection_chartVectorField D DE p (c.map_source hsource) hmetric
        (fderiv ℝ G x u) (fderiv ℝ G x v)
    rw [hcinv] at ht
    exact ht
  rw [hramp, hkderiv, hpush, hdf, hconn]
  have he := congrArg (mfderiv (𝓡 n) (𝓡 n) c.symm (G x))
    (covariantDerivativeAlongMap_fderiv_const DE hGx u v)
  simpa +instances only [covariantDerivativeAlongMap, map_add, C, c, G] using! he

end PoincareConjecture.M65Gauss
