import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUHopfCoordinates
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m64ChartPairing_eq_gram (g : RiemannianMetric n M) (q : M)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {f : LoopPlane → M}
    {p : LoopPlane} (hu : DifferentiableAt ℝ u p)
    (hut : u p ∈ (extChartAt (𝓡 n) q).target)
    (hmap : ((extChartAt (𝓡 n) q).symm ∘ u) =ᶠ[𝓝 p] f) (i j : Fin 2) :
    g.pullbackCoefficients (extChartAt (𝓡 n) q).symm (u p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
        m60AreaGram g f p i j := by
  let c := extChartAt (𝓡 n) q
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds hut)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp p hc (mdifferentiableAt_iff_differentiableAt.mpr hu)
  rw [mfderiv_eq_fderiv] at hd
  have heq := hmap.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 n)
  have hp : c.symm (u p) = f p := hmap.self_of_nhds
  change g.inner (c.symm (u p))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (u p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (u p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ j))) = _
  rw [m60AreaGram, ← heq, hd]
  exact congrArg (fun z : M => g.inner z
    (mfderiv (𝓡 n) (𝓡 n) c.symm (u p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    (mfderiv (𝓡 n) (𝓡 n) c.symm (u p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ j)))) hp




theorem m64LocalHarmonicMap_stress_cauchyRiemann (g : RiemannianMetric n M) (q : M)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {f : LoopPlane → M}
    {O : Set LoopPlane} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (hut : MapsTo u O (extChartAt (𝓡 n) q).target)
    (hmap : EqOn ((extChartAt (𝓡 n) q).symm ∘ u) f O)
    {p : LoopPlane} (hp : p ∈ O)
    (hharm : (∑ i : Fin 2,
      covDerivAlong (christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm)) u
        (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) p) = 0) :
    let G := m60AreaGram g f
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    fderiv ℝ (fun z => G z 0 0 - G z 1 1) p (e 0) =
        fderiv ℝ (fun z => -2 * G z 0 1) p (e 1) ∧
      fderiv ℝ (fun z => G z 0 0 - G z 1 1) p (e 1) =
        -fderiv ℝ (fun z => -2 * G z 0 1) p (e 0) := by
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hup := hu.contDiffAt (hO.mem_nhds hp)
  have hB : ContDiffAt ℝ ∞ B (u p) := (g.contDiffOn_chartCoefficients q).contDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (hut hp))
  have hdu (i : Fin 2) : ContDiffAt ℝ ∞ (fun z => fderiv ℝ u z (e i)) p :=
    (hup.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hcompat (v : LoopPlane) (b d : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun z => B (u z) b d) p v =
        B (u p) (christoffelBilinear B (u p) (fderiv ℝ u p v) b) d +
          B (u p) b (christoffelBilinear B (u p) (fderiv ℝ u p v) d) := by
    have hd := (((hB.differentiableAt (by simp)).hasFDerivAt.comp p
      (hup.differentiableAt (by simp)).hasFDerivAt).clm_apply
      (hasFDerivAt_const b p)).clm_apply (hasFDerivAt_const d p)
    dsimp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add]
    exact isMetricCompatibleAt_chartCoefficients g q (hut hp) _ _ _
  have htor := covDerivAlong_fderiv_symm
    (hup.of_le (WithTop.coe_le_coe.mpr le_top))
    (christoffelBilinear_chart_symm g q (u p)) (e 0) (e 1)
  have hcr := M60.harmonic_pairing_cauchyRiemann
    (Γ := M60.mapConnectionCoefficients (christoffelBilinear B) u) (e 0) (e 1)
    ((hB.comp p hup).differentiableAt (by simp))
    ((hdu 0).differentiableAt (by simp)) ((hdu 1).differentiableAt (by simp))
    hcompat (fun _ _ => g.symm _ _ _) htor
    (by simpa only [M60.covariantDerivative_mapConnectionCoefficients, Fin.sum_univ_two]
      using hharm)
  have hpair (i j : Fin 2) :
      (fun z => B (u z) (fderiv ℝ u z (e i)) (fderiv ℝ u z (e j))) =ᶠ[𝓝 p]
        (fun z => m60AreaGram g f z i j) := by
    filter_upwards [hO.mem_nhds hp] with z hz
    exact m64ChartPairing_eq_gram g q
      ((hu.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) (hut hz)
      (hmap.eventuallyEq_of_mem (hO.mem_nhds hz)) i j
  have hA := (hpair 0 0).sub (hpair 1 1)
  have hC := (EventuallyEq.refl (𝓝 p) (fun _ : LoopPlane => (-2 : ℝ))).mul (hpair 0 1)
  dsimp only [Function.comp_def] at hcr
  erw [hA.fderiv_eq (𝕜 := ℝ), hC.fderiv_eq (𝕜 := ℝ)] at hcr
  exact hcr

end PoincareConjecture
