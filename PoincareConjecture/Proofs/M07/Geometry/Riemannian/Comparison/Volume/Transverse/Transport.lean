import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem manifoldCovDerivAlong_congr_field
    (g : RiemannianMetric n M) (q : ℝ → M)
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (h : V =ᶠ[𝓝 t] W) :
    manifoldCovDerivAlong g q V 1 t = manifoldCovDerivAlong g q W 1 t := by
  unfold manifoldCovDerivAlong
  dsimp only
  apply congrArg
    (fun z => (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q t)).inverse z)
  exact covDerivAlong_congr _ _
    (h.mono fun s hs => congrArg
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q s)) hs) 1

theorem manifoldCovDerivAlong_twice_congr_field
    (g : RiemannianMetric n M) (q : ℝ → M)
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (h : V =ᶠ[𝓝 t] W) :
    manifoldCovDerivAlong g q (manifoldCovDerivAlong g q V 1) 1 t =
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q W 1) 1 t := by
  apply g.manifoldCovDerivAlong_congr_field q
  filter_upwards [h.eventually_nhds] with s hs
  exact g.manifoldCovDerivAlong_congr_field q hs

theorem radialDifferential_covariant_jacobi
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hgeo : ∀ v, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (v : EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t • v ∈ U) :
    let q := fun s : ℝ => e (s • v)
    let J := fun s : ℝ => mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w)
    manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
      -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
  let f : ℝ × ℝ → EuclideanSpace ℝ (Fin n) := fun p => p.2 • (v + p.1 • w)
  have hf : ContDiff ℝ ∞ f := by fun_prop
  have hnear : f ⁻¹' U ∈ 𝓝 (0, t) :=
    hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa [f] using ht))
  obtain ⟨S, I, hS, h0, hI, htI, hsub⟩ := mem_nhds_prod_iff'.mp hnear
  have hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (e ∘ f) (S ×ˢ I) := by
    intro p hp
    exact ((he.contMDiffAt (hU.mem_nhds (hsub hp))).comp p
      hf.contMDiff.contMDiffAt).contMDiffWithinAt
  have hg : ∀ s ∈ S, g.IsGeodesicOn (fun r => (e ∘ f) (s, r)) I := by
    intro s hs r hr
    apply hgeo (v + s • w) r
    exact hsub (show (s, r) ∈ S ×ˢ I from ⟨hs, hr⟩)
  have hjac := manifoldVariation_jacobi g D hS hI h0 hu hg htI
  dsimp only [Function.comp_def, f] at hjac
  change (manifoldCovDerivAlong g (fun r => e (r • (v + 0 • w)))
    (manifoldCovDerivAlong g (fun r => e (r • (v + 0 • w)))
      (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (r • (v + s • w))) 0 1) 1) 1 t :
        EuclideanSpace ℝ (Fin n)) +
      D.curvature (e (t • (v + 0 • w)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • (v + 0 • w))) t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun r : ℝ => e (r • (v + 0 • w))) t 1) = 0 at hjac
  erw [zero_smul, add_zero] at hjac
  have hfield :
      (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (r • (v + s • w))) 0 1)
        =ᶠ[𝓝 t] (fun r => mfderiv (𝓡 n) (𝓡 n) e (r • v) (r • w)) := by
    filter_upwards [hI.mem_nhds htI] with r hr
    have hmem : r • v ∈ U := by
      simpa [f] using hsub (show (0, r) ∈ S ×ˢ I from ⟨h0, hr⟩)
    exact radialVariation_field_eq v w r
      ((he.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt (by simp))
  erw [g.manifoldCovDerivAlong_twice_congr_field _ hfield] at hjac
  erw [radialVariation_field_eq v w t
    ((he.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp))] at hjac
  exact eq_neg_of_add_eq_zero_left hjac

theorem isGeodesicOn_all_rays_of_neighborhood
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ∈ 𝓝 0)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (v : EuclideanSpace ℝ (Fin n)) :
    g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U} := by
  have hline : Tendsto (fun r : ℝ => r • v) (𝓝 0) (𝓝 0) := by
    have h := (show Continuous (fun r : ℝ => r • v) by fun_prop).continuousAt (x := (0 : ℝ))
    change Tendsto (fun r : ℝ => r • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) at h
    simpa only [zero_smul] using h
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0, r • v ∈ U := nhdsWithin_le_nhds (hline hU)
  obtain ⟨r, hr, hrU⟩ := (hnear.and self_mem_nhdsWithin).exists
  have hr0 : r ≠ 0 := ne_of_gt hrU
  have hscale := (hgeo (r • v) hr).comp_mul r⁻¹
  have heq (s : ℝ) : (r⁻¹ * s) • (r • v) = s • v := by
    rw [smul_smul]
    congr 1
    field_simp
  simpa only [Set.preimage_ofPred_eq, heq] using hscale

theorem contDiffAt_chartField_radialDifferential
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (v w : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t • v ∈ U)
    {a : M} (ha : e (t • v) ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ (chartField (fun s => e (s • v)) a
      (fun s => mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w))) t := by
  let c := extChartAt (𝓡 n) a
  have het := he.contMDiffAt (hU.mem_nhds ht)
  have hf : ContDiffAt ℝ ∞ (c ∘ e) (t • v) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using ha)).comp
        (t • v) het)
  have hline : ContDiff ℝ ∞ (fun s : ℝ => s • v) := by fun_prop
  have hnear : ∀ᶠ s in 𝓝 t, s • v ∈ U ∧ e (s • v) ∈ c.source :=
    (hline.continuous.continuousAt).preimage_mem_nhds
      (inter_mem (hU.mem_nhds ht) (het.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source a).mem_nhds ha)))
  have hrep : (chartField (fun s => e (s • v)) a
      (fun s => mfderiv (𝓡 n) (𝓡 n) e (s • v) (s • w))) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ (c ∘ e) (s • v) (s • w)) := by
    filter_upwards [hnear] with s hs
    have hd := mfderiv_comp (s • v)
      (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hs.2))
      ((he.contMDiffAt (hU.mem_nhds hs.1)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact (congrArg (fun A => A (s • w)) hd).symm
  exact (((hf.fderiv_right (by simp)).comp t hline.contDiffAt).clm_apply
    (by fun_prop)).congr_of_eventuallyEq hrep

theorem contDiffAt_inverse_frame_field
    {q : ℝ → M}
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {J : (s : ℝ) → TangentSpace (𝓡 n) (q s)} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hPi : (P t).IsInvertible)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t)
    (hJ : ContDiffAt ℝ ∞ (chartField q (q t) J) t) :
    ContDiffAt ℝ ∞ (fun s => (P s).inverse (J s)) t := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q s)
  let Q := fun s => (L s).comp (P s)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply hP
  have hL : (L t).IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source _)
  have hi := ((hL.comp hPi).contDiffAt_map_inverse (n := ∞)).comp t hQ
  have hrep : (fun s => (P s).inverse (J s)) =ᶠ[𝓝 t]
      (fun s => (Q s).inverse (chartField q (q t) J s)) := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds (mem_extChartAt_source _))]
      with s hs
    have hLs : (L s).IsInvertible := isInvertible_mfderiv_extChartAt hs
    change (P s).inverse (J s) = ((L s).comp (P s)).inverse (L s (J s))
    rw [hLs.inverse_comp_apply_of_left, hLs.inverse_apply_self]
  exact (hi.clm_apply hJ).congr_of_eventuallyEq hrep

end PoincareConjecture.RiemannianMetric
