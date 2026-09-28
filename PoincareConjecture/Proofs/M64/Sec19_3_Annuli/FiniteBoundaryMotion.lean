import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteBoundaryParameters
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedC1Admission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]






theorem m64Annulus_exists_finite_boundary_motion
    {g : RiemannianMetric n M} (c0 c1 : ℝ → ℝ → M)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (hsigma0 : ContDiff ℝ 1 sigma0.map) (hsigma1 : ContDiff ℝ 1 sigma1.map)
    (A : M64Annulus g (c0 0 ∘ sigma0.map) (c1 0 ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry c0)
      (Ioo (-epsilon) epsilon ×ˢ univ))
    (hc1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry c1)
      (Ioo (-epsilon) epsilon ×ˢ univ))
    (hp0 : ∀ s, Function.Periodic (c0 s) curvePeriod)
    (hp1 : ∀ s, Function.Periodic (c1 s) curvePeriod) :
    ∃ d : ℕ, ∃ h : LoopPlane → EuclideanSpace ℝ (Fin d),
      ContDiffOn ℝ 1 h m64AnnulusDomain ∧
      ∃ delta : ℝ, 0 < delta ∧ ∃ O : Set (EuclideanSpace ℝ (Fin d)),
        IsOpen O ∧ MapsTo h m64AnnulusDomain O ∧
        ∃ Phi : ℝ × EuclideanSpace ℝ (Fin d) → M,
          ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 d)) (𝓡 n) ∞ Phi
            (Ioo (-delta) delta ×ˢ O) ∧
          (∀ p, Phi (0, h p) = A.map p) ∧
          (∀ s x y, Phi (s, h (annulusPoint (x + curvePeriod) y)) =
            Phi (s, h (annulusPoint x y))) ∧
          (∀ s x, Phi (s, h (annulusPoint x 0)) = c0 s (sigma0.map x)) ∧
          (∀ s x, Phi (s, h (annulusPoint x 1)) = c1 s (sigma1.map x)) ∧
          ∀ s ∈ Ioo (-delta) delta, ∀ g' : RiemannianMetric n M,
            ∃ B : M64Annulus g' (c0 s ∘ sigma0.map) (c1 s ∘ sigma1.map),
              EqOn B.map (fun p => Phi (s, h p)) m64AnnulusDomain ∧
              B.area = m64AnnulusArea g' (fun p => Phi (s, h p)) := by
  let : Nonempty M := ⟨A.map 0⟩
  obtain ⟨d, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨V, rho, hV, heV, hrho, hrhoe, -, -⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  let h := m64BoundaryMotionParameters e A.map sigma0.map sigma1.map
  let W := m64BoundaryDisplacement e c0 c1
  let Phi := rho ∘ W
  have hh : ContDiffOn ℝ 1 h m64AnnulusDomain :=
    m64BoundaryMotionParameters_contDiffOn he hA hsigma0 hsigma1
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hW := m64BoundaryDisplacement_contDiffOn he hzero c0 c1 hc0 hc1
  have hWzero (p : LoopPlane) : W (0, h p) = e (A.map p) := by
    change m64BoundaryDisplacement e c0 c1
      (0, m64BoundaryMotionParameters e A.map sigma0.map sigma1.map p) = _
    rw [m64BoundaryDisplacement_parameters]
    simp only [sub_self, smul_zero, add_zero]
  let K := h '' m64AnnulusDomain
  have hK : IsCompact K := m64AnnulusDomain_isCompact.image_of_continuousOn hh.continuousOn
  have hopen : IsOpen ((Ioo (-epsilon) epsilon ×ˢ univ) ∩ W ⁻¹' V) :=
    hW.continuousOn.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_univ) hV
  have htube : ({0} : Set ℝ) ×ˢ K ⊆ (Ioo (-epsilon) epsilon ×ˢ univ) ∩ W ⁻¹' V := by
    rintro ⟨s, q⟩ ⟨hs, p, hp, rfl⟩
    rcases mem_singleton_iff.mp hs with rfl
    exact ⟨⟨hzero, mem_univ _⟩, by rw [mem_preimage, hWzero]; exact heV (mem_range_self _)⟩
  obtain ⟨J, O, hJ, hO, h0J, hKO, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton hK hopen htube
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hJ.mem_nhds (h0J (mem_singleton 0)))
  have hsmall : Ioo (-delta) delta ⊆ J := by
    intro s hs
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs
  have hsubset : Ioo (-delta) delta ×ˢ O ⊆
      (Ioo (-epsilon) epsilon ×ˢ univ) ∩ W ⁻¹' V :=
    (prod_mono_left hsmall).trans hprod
  have hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 (d + 3))) (𝓡 n) ∞ Phi
      (Ioo (-delta) delta ×ˢ O) := by
    have hregular := hrho.comp (hW.mono (hsubset.trans inter_subset_left)).contMDiffOn
      (fun _ hq => (hsubset hq).2)
    simpa +instances only [modelWithCornersSelf_prod, chartedSpaceSelf_prod] using! hregular
  have hmap : MapsTo h m64AnnulusDomain O := fun p hp => hKO (mem_image_of_mem h hp)
  have hbase (p : LoopPlane) : Phi (0, h p) = A.map p := by
    change rho (W (0, h p)) = A.map p
    rw [hWzero, hrhoe]
  have hformula (s : ℝ) (p : LoopPlane) : Phi (s, h p) =
      rho (e (A.map p) + (1 - p 1) •
        (e (c0 s (sigma0.map (p 0))) - e (c0 0 (sigma0.map (p 0)))) +
        p 1 • (e (c1 s (sigma1.map (p 0))) - e (c1 0 (sigma1.map (p 0))))) :=
    congrArg rho (m64BoundaryDisplacement_parameters e c0 c1 A.map sigma0.map sigma1.map s p)
  have hper (s x y : ℝ) : Phi (s, h (annulusPoint (x + curvePeriod) y)) =
      Phi (s, h (annulusPoint x y)) := by
    rw [hformula, hformula, A.periodic]
    change rho (e (A.map (annulusPoint x y)) + (1 - y) •
      (e (c0 s (sigma0.map (x + curvePeriod))) - e (c0 0 (sigma0.map (x + curvePeriod)))) +
      y • (e (c1 s (sigma1.map (x + curvePeriod))) - e (c1 0 (sigma1.map (x + curvePeriod))))) = _
    rw [sigma0.period_shift, sigma1.period_shift, hp0 s (sigma0.map x),
      hp0 0 (sigma0.map x), hp1 s (sigma1.map x), hp1 0 (sigma1.map x)]
    rfl
  have hlo (s x : ℝ) : Phi (s, h (annulusPoint x 0)) = c0 s (sigma0.map x) := by
    rw [hformula, A.lower_boundary]
    change rho (e (c0 0 (sigma0.map x)) + (1 - (0 : ℝ)) •
      (e (c0 s (sigma0.map x)) - e (c0 0 (sigma0.map x))) +
      (0 : ℝ) • (e (c1 s (sigma1.map x)) - e (c1 0 (sigma1.map x)))) = _
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    have heq : e (c0 0 (sigma0.map x)) +
        (e (c0 s (sigma0.map x)) - e (c0 0 (sigma0.map x))) = e (c0 s (sigma0.map x)) := by abel
    rw [heq, hrhoe]
  have hhi (s x : ℝ) : Phi (s, h (annulusPoint x 1)) = c1 s (sigma1.map x) := by
    rw [hformula, A.upper_boundary]
    change rho (e (c1 0 (sigma1.map x)) + (1 - (1 : ℝ)) •
      (e (c0 s (sigma0.map x)) - e (c0 0 (sigma0.map x))) +
      (1 : ℝ) • (e (c1 s (sigma1.map x)) - e (c1 0 (sigma1.map x)))) = _
    simp only [sub_self, zero_smul, add_zero, one_smul]
    have heq : e (c1 0 (sigma1.map x)) +
        (e (c1 s (sigma1.map x)) - e (c1 0 (sigma1.map x))) = e (c1 s (sigma1.map x)) := by abel
    rw [heq, hrhoe]
  refine ⟨d + 3, h, hh, delta, hdelta, O, hO, hmap, Phi, hPhi, hbase, hper, hlo, hhi, ?_⟩
  intro s hs g'
  have hslice : ContMDiffOn (𝓡 2) (𝓡 n) 1 (fun p => Phi (s, h p)) m64AnnulusDomain :=
    (hPhi.of_le (by simp)).comp (contMDiffOn_const.prodMk hh.contMDiffOn)
      (fun _ hp => ⟨hs, hmap hp⟩)
  have hperiod0 : Function.Periodic (c0 s ∘ sigma0.map) curvePeriod := by
    intro x
    simp only [Function.comp_apply, sigma0.period_shift]
    exact hp0 s (sigma0.map x)
  have hperiod1 : Function.Periodic (c1 s ∘ sigma1.map) curvePeriod := by
    intro x
    simp only [Function.comp_apply, sigma1.period_shift]
    exact hp1 s (sigma1.map x)
  obtain ⟨B, hB⟩ := m64Annulus_exists_eqOn_rectangle_of_contMDiffOn g' hperiod0 hperiod1
    (fun p => Phi (s, h p)) hslice
    (fun y _ => by simpa only [zero_add] using hper s 0 y)
    (fun x _ => hlo s x) (fun x _ => hhi s x)
  exact ⟨B, hB, integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g' hB)⟩

end PoincareConjecture
