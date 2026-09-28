import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryGreenAssembly
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundaryComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryParameterLabels














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ
local notation "S" => interior m64AnnulusDomain
local notation "I" => Icc (0 : ℝ) curvePeriod




theorem local_energy_le_of_halfDisk_data {n m : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : M → EuclideanSpace ℝ (Fin m)}
    {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
    {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (Q : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hQ : Continuous Q) (hei : IsEmbedding e) {bound : ℝ}
    (hb : ∀ q, ‖Q q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ Q q v v)
    {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q modulus ≤ C.annulus.weightedEnergy Q modulus)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    {x r : ℝ} (hr0 : 0 ≤ r) (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1)
    (sigma : ℝ → ℝ) (hsc : Continuous sigma) (hsm : Monotone sigma)
    (hsp : ∀ y, sigma (y + curvePeriod) = sigma y + curvePeriod) (hsn : sigma 0 ∈ I)
    (hsout : EqOn sigma A.label0 (I \ Icc (x - r) (x + r)))
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (u : LoopPlane → ℝ) (W : Fin 2 → LoopPlane → ℝ)
    (hf : MemLp (e ∘ f) 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hV : ∀ i, MemLp (V i) 2
      (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hu : MemLp u 2 (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hW : ∀ i, MemLp (W i) 2
      (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (ht : ∀ i, ∀ z ∈ closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      V i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f z)))
    (hobs : ∀ z ∈ closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      R (e (f z)) = angularPoint (k * u z))
    (hgreen : ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ (i : Fin 2) (j : Fin m),
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        V i z j * test z + e (f z) j * fderiv ℝ test z (basis i)) =
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        A.annulus.column i (z + annulusPoint x 0) j * test z +
          e (A.annulus.map (z + annulusPoint x 0)) j * fderiv ℝ test z (basis i)) +
      (basis 1) i *
        ((∫ s in (-r)..r, e (c0 (A.label0 (s + x))) j * test (s • basis 0)) -
          ∫ s in (-r)..r, e (c0 (sigma (s + x))) j * test (s • basis 0)))
    (hphase : ∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        W i z * test z + u z * fderiv ℝ test z (basis i)) =
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        A.phaseColumn i (z + annulusPoint x 0) * test z +
          A.phase (z + annulusPoint x 0) * fderiv ℝ test z (basis i)) +
      (basis 1) i *
        ((∫ s in (-r)..r, H0 (A.label0 (s + x)) * test (s • basis 0)) -
          ∫ s in (-r)..r, H0 (sigma (s + x)) * test (s • basis 0))) :
    (∫ p in closedBall (annulusPoint x 0) r ∩ S,
      (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
        Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      (max modulus modulus⁻¹) ^ 2 *
        ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
          (Q (f z) (V 0 z) (V 0 z) + Q (f z) (V 1 z) (V 1 z)) / 2 := by
  classical
  let K := closedBall (annulusPoint x 0) r ∩ S
  let F := fun p => f (p - annulusPoint x 0)
  let Z := fun i p => V i (p - annulusPoint x 0)
  have hK : MeasurableSet K := measurableSet_closedBall.inter isOpen_interior.measurableSet
  have hKS : K ⊆ S := inter_subset_right
  have hF : MemLp (e ∘ F) 2 (volume.restrict K) := m64Annulus_boundary_disk_memLp hf
  have hZ (i : Fin 2) : MemLp (Z i) 2 (volume.restrict K) :=
    m64Annulus_boundary_disk_memLp (hV i)
  obtain ⟨hl0, hl1⟩ := A.labels_continuous hH0 hH1
  have hcompare : (∫ p in K,
      (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
        Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      (max modulus modulus⁻¹) ^ 2 *
        ∫ p in K, (Q (F p) (Z 0 p) (Z 0 p) + Q (F p) (Z 1 p) (Z 1 p)) / 2 := by
    apply A.local_energy_le_of_boundary_flux Q hQ hei hb hpos hmod hminimum
      hsm A.label1_monotone hsp A.label1_period hsn A.label1_normalized
      hK hKS F Z hF hZ
    · intro i
      exact ae_restrict_of_forall_mem hK (fun p hp =>
        ht i _ (m64Annulus_boundary_disk_sub_mem hp))
    · intro phi hphi i
      have holdU := A.annulus.observed_memLp.mono_measure (Measure.restrict_mono hKS le_rfl)
      have holdV := (Lp.memLp (A.annulus.column i)).mono_measure
        (Measure.restrict_mono hKS le_rfl)
      have hg := m64Annulus_boundary_vector_green hr0 hx hP hr (e ∘ f) (V i)
        (e ∘ A.annulus.map) (A.annulus.column i) (e ∘ c0 ∘ A.label0) (e ∘ c0 ∘ sigma) i
        hf (hV i) holdU holdV (hc0.comp hl0).continuousOn (hc0.comp hsc).continuousOn
        (fun y hy => congrArg (fun t => e (c0 t)) (hsout hy).symm)
        (fun test htest j => hgreen test htest i j) phi hphi
      have hc (s : ℝ) := hphi.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
      have htop : IntegrableOn (fun y => phi (annulusPoint y 1) • e (c1 (A.label1 y))) I :=
        ((hc 1).smul (hc1.comp hl1)).continuousOn.integrableOn_compact isCompact_Icc
      have hold : IntegrableOn (fun y => phi (annulusPoint y 0) • e (c0 (A.label0 y))) I :=
        ((hc 0).smul (hc0.comp hl0)).continuousOn.integrableOn_compact isCompact_Icc
      have hnew : IntegrableOn (fun y => phi (annulusPoint y 0) • e (c0 (sigma y))) I :=
        ((hc 0).smul (hc0.comp hsc)).continuousOn.integrableOn_compact isCompact_Icc
      have hflux : (∫ y in I, phi (annulusPoint y 1) • e (c1 (A.label1 y)) -
          phi (annulusPoint y 0) • e (c0 (sigma y))) -
          (∫ y in I, phi (annulusPoint y 1) • e (c1 (A.label1 y)) -
            phi (annulusPoint y 0) • e (c0 (A.label0 y))) =
          (∫ y in I, phi (annulusPoint y 0) • e (c0 (A.label0 y))) -
            ∫ y in I, phi (annulusPoint y 0) • e (c0 (sigma y)) := by
        rw [integral_sub htop hnew, integral_sub htop hold]
        abel
      rw [hflux]
      simpa only [EuclideanSpace.basisFun_apply, Function.comp_apply, K, F, Z] using hg
    · exact m64Annulus_boundary_disk_memLp hu
    · intro i
      exact m64Annulus_boundary_disk_memLp (hW i)
    · intro phi hphi i
      have holdU := (Lp.memLp A.phase).mono_measure (Measure.restrict_mono hKS le_rfl)
      have holdV := (Lp.memLp (A.phaseColumn i)).mono_measure (Measure.restrict_mono hKS le_rfl)
      have hg := m64Annulus_boundary_scalar_green hr0 hx hP hr u (W i) A.phase (A.phaseColumn i)
        (H0 ∘ A.label0) (H0 ∘ sigma) i hu (hW i) holdU holdV
        (H0.continuous.comp hl0).continuousOn (H0.continuous.comp hsc).continuousOn
        (fun y hy => congrArg H0 (hsout hy).symm)
        (fun test htest => hphase test htest i) phi hphi
      have hc (s : ℝ) := hphi.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
      have htop : IntegrableOn (fun y => phi (annulusPoint y 1) *
          (H1 (A.label1 y) + A.offset)) I :=
        ((hc 1).mul ((H1.continuous.comp hl1).add continuous_const)).continuousOn
          |>.integrableOn_compact isCompact_Icc
      have hold : IntegrableOn (fun y => phi (annulusPoint y 0) * H0 (A.label0 y)) I :=
        ((hc 0).mul (H0.continuous.comp hl0)).continuousOn.integrableOn_compact isCompact_Icc
      have hnew : IntegrableOn (fun y => phi (annulusPoint y 0) * H0 (sigma y)) I :=
        ((hc 0).mul (H0.continuous.comp hsc)).continuousOn.integrableOn_compact isCompact_Icc
      have hflux : (∫ y in I, phi (annulusPoint y 1) * (H1 (A.label1 y) + A.offset) -
          phi (annulusPoint y 0) * H0 (sigma y)) -
          (∫ y in I, phi (annulusPoint y 1) * (H1 (A.label1 y) + A.offset) -
            phi (annulusPoint y 0) * H0 (A.label0 y)) =
          (∫ y in I, phi (annulusPoint y 0) * H0 (A.label0 y)) -
            ∫ y in I, phi (annulusPoint y 0) * H0 (sigma y) := by
        rw [integral_sub htop hnew, integral_sub htop hold]
        ring
      rw [hflux]
      simpa only [EuclideanSpace.basisFun_apply, Function.comp_apply, K] using hg
    · filter_upwards [A.phase_observation] with p hp
      by_cases hmem : p ∈ K
      · simp only [piecewise, if_pos hmem]
        exact hobs _ (m64Annulus_boundary_disk_sub_mem hmem)
      · simpa only [piecewise, if_neg hmem] using hp
  apply hcompare.trans_eq
  congr 1
  rw [m64Annulus_boundary_disk_integral hx hP hr]
  simp only [F, Z, add_sub_cancel_right]

end PoincareConjecture.M64FreeWeakPhaseAnnulus
