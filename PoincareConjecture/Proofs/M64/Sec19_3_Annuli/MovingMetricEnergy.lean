import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurrent
import PoincareConjecture.Proofs.M62.Sec19_1_MetricVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

noncomputable def m64MixedAnnulusEnergy
    (F : RicciFlow n M (Icc a b)) (v : ℝ × LoopPlane → M)
    (q : ℝ × (ℝ × LoopPlane)) : ℝ :=
  m60EnergyDensity (F.metric q.1) (fun z => v (q.2.1, z)) q.2.2

theorem m64MixedAnnulusEnergy_contDiffAt
    (F : RicciFlow n M (Icc a b)) {v : ℝ × LoopPlane → M}
    {q : ℝ × (ℝ × LoopPlane)} (ht : q.1 ∈ Ioo a b)
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v q.2) :
    ContDiffAt ℝ ∞ (m64MixedAnnulusEnergy F v) q := by
  let u (i : Fin 2) (w : ℝ × LoopPlane) :=
    mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v w
      (0, EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hpush (i : Fin 2) :
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) ((𝓡 n).prod (𝓡 n)) ∞
        (fun w => (⟨v w, u i w⟩ : TangentBundle (𝓡 n) M)) q.2 := by
    have hd : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane)
        ((𝓘(ℝ, ℝ × LoopPlane)).prod 𝓘(ℝ, ℝ × LoopPlane)) ∞
        (fun w : ℝ × LoopPlane =>
          (⟨w, (0, EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
            TangentBundle 𝓘(ℝ, ℝ × LoopPlane) (ℝ × LoopPlane))) q.2 := by
      rw [contMDiffAt_totalSpace]
      refine ⟨contMDiffAt_id, ?_⟩
      simpa using contMDiffAt_const
        (c := ((0 : ℝ), EuclideanSpace.basisFun (Fin 2) ℝ i))
    exact (hv.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hd hv
  have hdomain : Icc a b ×ˢ (univ : Set M) ∈ 𝓝 (q.1, v q.2) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem
  have hmetric := (F.smooth.contMDiffAt hdomain).comp q
    (contDiffAt_fst.contMDiffAt.prodMk (hv.comp q contDiffAt_snd.contMDiffAt))
  have hscalar (i : Fin 2) : ContDiffAt ℝ ∞
      (fun w : ℝ × (ℝ × LoopPlane) =>
        (F.metric w.1).inner (v w.2) (u i w.2) (u i w.2)) q := by
    have h := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
      ((hpush i).comp q contDiffAt_snd.contMDiffAt)
      ((hpush i).comp q contDiffAt_snd.contMDiffAt)
    exact contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp h).2
  have hraw := (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((hscalar 0).add (hscalar 1))
  apply hraw.congr_of_eventuallyEq
  have hnear : ∀ᶠ w in 𝓝 q.2, ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) 1 v w :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hv.of_le (by simp))
  filter_upwards [(continuous_snd.tendsto q).eventually hnear] with w hw
  have hmd := hw.mdifferentiableAt one_ne_zero
  simp only [m64MixedAnnulusEnergy, m60EnergyDensity, Matrix.trace, Fin.sum_univ_two,
    m60AreaGram, m64MovingAnnulus_spatial_differential hmd, u]
  rfl

theorem m64Annulus_moving_metric_energy_hasDerivAt
    (F : RicciFlow n M (Icc a b)) {v : ℝ × LoopPlane → M}
    {t : ℝ} (ht : t ∈ Ioo a b) (p : LoopPlane)
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v (0, p)) :
    let d := mfderiv (𝓡 2) (𝓡 n) (fun z => v (0, z)) p
    HasDerivAt (fun r => m60EnergyDensity (F.metric (t + r)) (fun z => v (r, z)) p)
      (deriv (fun r => m60EnergyDensity (F.metric t) (fun z => v (r, z)) p) 0 -
        (F.connection t).ricci (v (0, p))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 0)) -
        (F.connection t).ricci (v (0, p))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))) 0 := by
  let E := m64MixedAnnulusEnergy F v
  let d := mfderiv (𝓡 2) (𝓡 n) (fun z => v (0, z)) p
  let u := fun i : Fin 2 => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let R := fun i : Fin 2 => (F.connection t).ricci (v (0, p)) (u i) (u i)
  have hE := (m64MixedAnnulusEnergy_contDiffAt F
    (q := (t, (0, p))) ht hv).differentiableAt (by simp)
  have hmetric := hE.hasFDerivAt.comp_hasDerivAt (l := E)
    (f := fun r : ℝ => (r, ((0 : ℝ), p))) t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t ((0 : ℝ), p)))
  have hmap := hE.hasFDerivAt.comp_hasDerivAt (l := E)
    (f := fun r : ℝ => (t, (r, p))) 0
    ((hasDerivAt_const 0 t).prodMk ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p)))
  have hE0 : HasFDerivAt E (fderiv ℝ E (t, (0, p))) (t + 0, (0, p)) := by
    simpa only [add_zero] using hE.hasFDerivAt
  have hdiag := hE0.comp_hasDerivAt (l := E)
    (f := fun r : ℝ => (t + r, (r, p))) 0
    (((hasDerivAt_id 0).const_add t).prodMk
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p)))
  have hric (i : Fin 2) : HasDerivAt
      (fun r => (F.metric r).inner (v (0, p)) (u i) (u i)) (-2 * R i) t :=
    (F.equation t (Ioo_subset_Icc_self ht) (v (0, p)) (u i) (u i)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hmetric' : HasDerivAt (fun r => E (r, (0, p))) (-R 0 - R 1) t := by
    have h := ((hric 0).add (hric 1)).const_mul (1 / 2 : ℝ)
    convert! h using 1
    · funext r
      simp only [E, m64MixedAnnulusEnergy, m60EnergyDensity, Matrix.trace,
        Fin.sum_univ_two, m60AreaGram, d, u, Pi.add_apply]
      rfl
    · ring
  have hmetric_value : fderiv ℝ E (t, (0, p)) (1, (0, 0)) = -R 0 - R 1 :=
    hmetric.unique hmetric'
  have hmap_value : fderiv ℝ E (t, (0, p)) (0, (1, 0)) =
      deriv (fun r => m60EnergyDensity (F.metric t) (fun z => v (r, z)) p) 0 :=
    hmap.deriv.symm
  change HasDerivAt (fun r => E (t + r, (r, p)))
    (deriv (fun r => m60EnergyDensity (F.metric t) (fun z => v (r, z)) p) 0 -
      R 0 - R 1) 0
  apply hdiag.congr_deriv
  rw [show ((1 : ℝ), ((1 : ℝ), (0 : LoopPlane))) =
    (1, (0, 0)) + (0, (1, 0)) by simp, map_add, hmetric_value, hmap_value]
  ring

end PoincareConjecture
