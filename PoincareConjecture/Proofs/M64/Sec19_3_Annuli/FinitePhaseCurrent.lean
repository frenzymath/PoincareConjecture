import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CirclePhaseDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteConformality






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem m64Annulus_affine_phase_within_current
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point}
    (hf : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 f m64AnnulusDomain)
    (hfi : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ f m64AnnulusInterior)
    {c : ℝ} (hphase : ∀ p ∈ m64AnnulusDomain,
      (f p).2 = P.circle.quotient (c * p 1)) :
    ∀ p ∈ m64AnnulusDomain,
      (P.flow.metric t).inner (f p)
        (mfderivWithin (𝓡 2) (𝓡 (n + 1)) f m64AnnulusDomain p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) (P.charts.circleUnit (f p)) = c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric t).toRiemannianMetric⟩
  let J : LoopPlane → ℝ := fun p => (P.flow.metric t).inner (f p)
    (mfderivWithin (𝓡 2) (𝓡 (n + 1)) f m64AnnulusDomain p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)) (P.charts.circleUnit (f p))
  have hc : ContinuousOn J m64AnnulusDomain :=
    (m64AnnulusWithinColumn_continuousOn hf 1).inner_bundle
      ((M62.circleProduct_identities P).circle_unit_smooth.continuous.comp_continuousOn
        hf.continuousOn)
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have heq : EqOn J (fun _ => c) m64AnnulusInterior := by
    intro p hp
    let L : LoopPlane →L[ℝ] ℝ := c • EuclideanSpace.proj (1 : Fin 2)
    have hquot : P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ f := by
      filter_upwards [isOpen_m64AnnulusInterior.mem_nhds hp] with q hq
      exact (hphase q (hsub hq)).symm
    have h := m64CirclePhase_current P t
      ((hfi.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)).mdifferentiableAt (by simp))
      L.differentiableAt hquot 1
    have hd : fderiv ℝ L p (EuclideanSpace.single (1 : Fin 2) 1) = c := by
      rw [L.fderiv]
      simp [L]
    rw [hd] at h
    have hpi := (interior_maximal hsub isOpen_m64AnnulusInterior) hp
    dsimp only [J]
    rw [mfderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hpi)]
    simpa only [m64AnnulusCircleCurrent, EuclideanSpace.basisFun_apply] using h.symm
  exact heq.of_subset_closure hc continuousOn_const hsub
    (by rw [m64AnnulusInterior_closure])





theorem m64Annulus_affine_phase_radial_ne_zero
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point}
    (hf : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 f m64AnnulusDomain)
    (hfi : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ f m64AnnulusInterior)
    {c : ℝ} (hc : c ≠ 0) (hphase : ∀ p ∈ m64AnnulusDomain,
      (f p).2 = P.circle.quotient (c * p 1)) :
    ∀ p ∈ m64AnnulusDomain,
      mfderivWithin (𝓡 2) (𝓡 (n + 1)) f m64AnnulusDomain p
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) ≠ 0 := by
  intro p hp hz
  have h := m64Annulus_affine_phase_within_current P t hf hfi hphase p hp
  rw [hz, map_zero, zero_apply] at h
  exact hc h.symm

end PoincareConjecture
