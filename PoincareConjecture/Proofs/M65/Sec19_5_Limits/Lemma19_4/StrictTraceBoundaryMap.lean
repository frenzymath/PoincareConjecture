import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceCoordinates
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHarmonicPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M65StrictTrace

open M65Branch





theorem exists_harmonic_boundary_halfDisk
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {G : LoopPlane → LoopAmbient} {O : Set LoopPlane} (hO : IsOpen O)
    {p : ℂ} (hp : ‖p‖ = 1) (hpO : orthonormalBasisOneI.repr p ∈ O)
    (hG : ContDiffOn ℝ 1 G (loopDiskSet ∩ O))
    (hGi : ContDiffOn ℝ ∞ G (ball (0 : LoopPlane) 1 ∩ O))
    (heq : ∀ z ∈ ball (0 : LoopPlane) 1 ∩ O,
      (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
        ∑ i : Fin 2, M65Gauss.connectionCoefficient D (G z)
          (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0)
    {V : Set LoopAmbient} (hV : IsOpen V) (hpV : G (orthonormalBasisOneI.repr p) ∈ V) :
    let P := orthonormalBasisOneI.repr ∘ boundaryCoordinate p
    let H := G ∘ P
    ∃ r : ℝ, 0 < r ∧
      MapsTo P (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (loopDiskSet ∩ O) ∧
      MapsTo P (ball (0 : ℂ) r ∩ {z | 0 < z.im}) (ball (0 : LoopPlane) 1 ∩ O) ∧
      MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) V ∧
      ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ∧
      ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
        dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := e ∘ boundaryCoordinate p
  let H := G ∘ P
  have hpK : e p ∈ loopDiskSet ∩ O := by
    refine ⟨?_, hpO⟩
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr p‖ ≤ 1
    rw [orthonormalBasisOneI.repr.norm_map, hp]
  have hP : ContDiff ℝ ∞ P := e.contDiff.comp
    ((contDiff_boundaryCoordinate p).restrict_scalars ℝ)
  have hP0 : P 0 = e p := by simp [P, boundaryCoordinate]
  have hcap : ∀ᶠ y in 𝓝[loopDiskSet ∩ O] (e p), G y ∈ V :=
    hG.continuousOn _ hpK (hV.mem_nhds hpV)
  obtain ⟨W, hW, hWcap⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hcap
  have hpre : ∀ᶠ z in 𝓝 (0 : ℂ), P z ∈ W ∩ O := by
    have hc : Tendsto P (𝓝 0) (𝓝 (e p)) := by
      simpa only [hP0] using hP.continuous.tendsto 0
    exact hc.eventually (inter_mem hW (hO.mem_nhds hpO))
  obtain ⟨eta, heta, hetacap⟩ := Metric.mem_nhds_iff.mp hpre
  let r := eta / 2
  have hr : 0 < r := half_pos heta
  have hball (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) : P z ∈ W ∩ O :=
    hetacap ((closedBall_subset_ball (by dsimp only [r]; linarith)) hz)
  have hclosed : MapsTo P (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im})
      (loopDiskSet ∩ O) := by
    intro z hz
    refine ⟨?_, (hball z hz.1).2⟩
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr (boundaryCoordinate p z)‖ ≤ 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (boundaryCoordinate_disk_iff hp z).mpr hz.2
  have hopen : MapsTo P (ball (0 : ℂ) r ∩ {z | 0 < z.im})
      (ball (0 : LoopPlane) 1 ∩ O) := by
    intro z hz
    refine ⟨?_, (hball z (ball_subset_closedBall hz.1)).2⟩
    rw [mem_ball_zero_iff]
    change ‖orthonormalBasisOneI.repr (boundaryCoordinate p z)‖ < 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (boundaryCoordinate_interior_iff hp z).mpr hz.2
  have htarget : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) V := by
    intro z hz
    exact hWcap ⟨(hball z hz.1).1, hclosed hz⟩
  have hC1 : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) :=
    hG.comp (hP.of_le (by simp)).contDiffOn hclosed
  have hCinf : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}) :=
    hGi.comp hP.contDiffOn hopen
  refine ⟨r, hr, hclosed, hopen, htarget, hC1, hCinf, ?_⟩
  let S := ball (0 : LoopPlane) 1 ∩ O
  let S' := e ⁻¹' S
  let T := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hS : IsOpen S := isOpen_ball.inter hO
  have hS' : IsOpen S' := hS.preimage e.continuous
  have hT : IsOpen T := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hGe : ContDiffOn ℝ ∞ (G ∘ e) S' :=
    hGi.comp e.contDiff.contDiffOn (fun _ hz => hz)
  have heq' (z : ℂ) (hz : z ∈ S') :
      dbar (complexGradient (G ∘ e)) z =
        harmonicMatrix D (G ∘ e) z (complexGradient (G ∘ e) z) :=
    plane_harmonic_to_complex D (hGi.contDiffAt (hS.mem_nhds hz)) (heq _ hz)
  intro z hz
  exact harmonic_matrix_equation_comp_holomorphic D hS' hT hGe
    (contDiff_boundaryCoordinate p).contDiffOn hopen heq' hz

end PoincareConjecture.M65StrictTrace
