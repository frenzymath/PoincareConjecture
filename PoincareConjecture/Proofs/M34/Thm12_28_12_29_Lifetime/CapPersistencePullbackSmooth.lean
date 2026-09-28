import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderPullback
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocality
import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizationModel
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem capPersistence_roundCylinderTensorSmoothOn_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {epsilon : ℝ} {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn Ic (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)) :
    RoundCylinderTensorSmoothOn epsilon (roundCylinderPullback g f) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  intro q a b x hx
  let ψ : RoundCylinderCoordinates → RoundCylinderSpace := fun y =>
    ((chartAt E₂ q).symm y.1, y.2)
  have hψ : ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) Ic ∞ ψ :=
    ((contMDiff_sphere_chart_symm (n := 2) (m := ∞) q).comp
      (ContinuousLinearMap.fst ℝ E₂ ℝ).contMDiff).prodMk
        (ContinuousLinearMap.snd ℝ E₂ ℝ).contMDiff
  let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hfx : ContMDiffAt Ic (𝓡 3) ∞ f (ψ x) :=
    hf.contMDiffAt (hU.mem_nhds ⟨mem_univ _, hx.2⟩)
  let φ := f ∘ ψ
  have hφ : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ φ x :=
    hfx.comp x (hψ x)
  have hscalar : ContDiffAt ℝ ∞ (fun y =>
      g.inner (φ y) (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y
        (roundCylinderCoordinateBasis a))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y
          (roundCylinderCoordinateBasis b))) x :=
    by
      have hg := (g.contMDiff (φ x)).comp x hφ
      have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
        (RiemannianMetric.contMDiffAt_mfderiv_const_vector hφ (roundCylinderCoordinateBasis a))
        (RiemannianMetric.contMDiffAt_mfderiv_const_vector hφ (roundCylinderCoordinateBasis b))
      apply contMDiffAt_iff_contDiffAt.mp
      simpa using (Bundle.contMDiffAt_totalSpace.mp h).2
  have heq : (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g f)
      (chartAt E₂ q) y a b) =ᶠ[𝓝 x] (fun y =>
      g.inner (φ y) (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y
        (roundCylinderCoordinateBasis a))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y
          (roundCylinderCoordinateBasis b))) := by
    have hnear := hψ.continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (show ψ x ∈ U from ⟨mem_univ _, hx.2⟩))
    filter_upwards [hnear] with y hy
    have hfy := (hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
    have hcs := ((contMDiff_sphere_chart_symm (n := 2) (m := ∞) q) y.1).mdifferentiableAt
      (by simp)
    let A := ContinuousLinearMap.fst ℝ E₂ ℝ
    let B := ContinuousLinearMap.snd ℝ E₂ ℝ
    have ha := hcs.comp y A.mdifferentiableAt
    have hb := B.mdifferentiableAt (x := y)
    have hpair : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) Ic ψ y =
        ((mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm y.1).comp A).prod B := by
      calc
        _ = (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2)
            ((chartAt E₂ q).symm ∘ A) y).prod
              (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) B y) :=
          mfderiv_prodMk ha hb
        _ = _ := congrArg₂ (fun L K => L.prod K)
          ((mfderiv_comp y hcs A.mdifferentiableAt).trans
            (congrArg (fun L => (mfderiv (𝓡 2) (𝓡 2)
              (chartAt E₂ q).symm y.1).comp L) A.mfderiv_eq)) B.mfderiv_eq
    have hd : ∀ v : RoundCylinderCoordinates,
        mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y v =
          mfderiv Ic (𝓡 3) f (ψ y)
            (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm y.1 v.1, v.2) := by
      intro v
      have hh : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ y =
          (mfderiv Ic (𝓡 3) f (ψ y)).comp
            (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) Ic ψ y) :=
        mfderiv_comp y hfy (ha.prodMk hb)
      exact congrArg (fun L => L v) (hh.trans
        (congrArg (fun L => (mfderiv Ic (𝓡 3) f (ψ y)).comp L) hpair))
    rw [hd, hd]
    rfl
  exact (hscalar.congr_of_eventuallyEq heq).contDiffWithinAt

theorem capPersistence_generalizedCylinderPullback_smooth
    {G : GeneralizedRicciFlowData} {C : GeneralizedSliceCarrier}
    {origin scale : ℝ} {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder G C origin scale K U) (hU : IsOpen U)
    {epsilon : ℝ} {f : RoundCylinderSpace → C.carrier}
    (hf : ContMDiffOn Ic (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (hcap : MapsTo f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) U)
    {s : ℝ} (hs : s ∈ K) :
    RoundCylinderTensorSmoothOn epsilon (generalizedCylinderPullback e f s) := by
  have hcomp := (e.forward_smooth s hs).comp hf hcap
  have hb := (capPersistence_roundCylinderTensorSmoothOn_pullback
    (G.metric (origin + s / scale)) hcomp).const_mul (beta := scale)
  apply hb.congr_cylinder
  intro z hz v w
  have hφ := (hf.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have he := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hcap ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos hs, roundCylinderPullback]
  rw [mfderiv_comp z he hφ]
  rfl

end PoincareConjecture.M34
