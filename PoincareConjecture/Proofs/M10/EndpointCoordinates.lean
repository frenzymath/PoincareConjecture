import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Proofs.M10.ProductDerivatives
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def endpointCoordinates (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ) : EuclideanSpace ℝ (Fin n) :=
  extChartAt (𝓡 n) q₀ (G.gamma z.1 z.2)

set_option backward.isDefEq.respectTransparency false in

theorem endpointCoordinates_contDiffAt (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContDiffAt ℝ ∞ (endpointCoordinates G q₀) z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have he := (contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hq).comp z hγ
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at he
  exact he.contDiffAt

set_option backward.isDefEq.respectTransparency false in

theorem endpointCoordinates_horizontal (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (h : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (endpointCoordinates G q₀) z (h, 0) =
      (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q₀).continuousLinearMapAt ℝ (G.gamma z.1 z.2)
        (G.toLExponentialFamily.sliceDifferential z.1 z.2 h) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  rw [fderiv_horizontal_eq
    ((endpointCoordinates_contDiffAt G q₀ z hz hq).differentiableAt (by simp)) h]
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have hs : MDifferentiableAt (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n)
      (fun Z ↦ G.gamma Z z.2) z.1 :=
    (hγ.comp z.1 (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp z.1 (mdifferentiableAt_extChartAt hq) hs
  rw [mfderiv_eq_fderiv] at hc
  change fderiv ℝ ((extChartAt (𝓡 n) q₀) ∘ (fun Z ↦ G.gamma Z z.2)) z.1 h = _
  rw [hc, ← TangentBundle.continuousLinearMapAt_trivializationAt hq]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem endpointCoordinates_time (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    fderiv ℝ (endpointCoordinates G q₀) z (0, 1) =
      (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q₀).continuousLinearMapAt ℝ (G.gamma z.1 z.2)
        (curveVelocity (G.gamma z.1) z.2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have hγ := G.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
  have ht : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (G.gamma z.1) z.2 :=
    (hγ.comp z.2 (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp z.2 (mdifferentiableAt_extChartAt hq) ht
  rw [mfderiv_eq_fderiv] at hc
  have hd := hasDerivAt_time_slice
    ((endpointCoordinates_contDiffAt G q₀ z hz hq).differentiableAt (by simp))
  rw [← hd.deriv]
  change fderiv ℝ ((extChartAt (𝓡 n) q₀) ∘ G.gamma z.1) z.2 1 = _
  rw [hc, ← TangentBundle.continuousLinearMapAt_trivializationAt hq]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem endpointCoordinates_horizontal_bijective (G : LExponentialGeometry F T τmax p)
    (q₀ : M) (z : TangentSpace (𝓡 n) p × ℝ)
    (hz : z ∈ univ ×ˢ Ioo 0 τmax)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (hcrit : Function.Bijective (G.toLExponentialFamily.sliceDifferential z.1 z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    Function.Bijective (fun h : TangentSpace (𝓡 n) p ↦
      fderiv ℝ (endpointCoordinates G q₀) z (h, 0)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let he := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) q₀).continuousLinearEquivAt ℝ (G.gamma z.1 z.2) hq
  have h := he.bijective.comp hcrit
  simpa only [he, Bundle.Trivialization.coe_continuousLinearEquivAt_eq,
    Function.comp_def, ← endpointCoordinates_horizontal G q₀ z hz hq] using h

end PoincareConjecture.M10
