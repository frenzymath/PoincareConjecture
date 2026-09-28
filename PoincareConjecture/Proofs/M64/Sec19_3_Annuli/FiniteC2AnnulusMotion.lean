import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteBoundaryMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteC2BoundaryReference





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}






theorem m64C2Annulus_exists_finite_energy_motion
    (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (hsigma0 : ContDiff ℝ 1 sigma0.map) (hsigma1 : ContDiff ℝ 1 sigma1.map)
    (A : M64Annulus (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ s ∈ Ioo (-epsilon) epsilon, t + s ∈ Ioo a b) ∧
      ∃ v : ℝ → LoopPlane → M,
        (∀ p, v 0 p = A.map p) ∧
        (∀ s x y, v s (annulusPoint (x + curvePeriod) y) = v s (annulusPoint x y)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ x,
          v s (annulusPoint x 0) = c0 (sigma0.map x) (t + s)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ x,
          v s (annulusPoint x 1) = c1 (sigma1.map x) (t + s)) ∧
        (∀ x, curveVelocity (n := n) (fun s => v s (annulusPoint x 0)) 0 =
          m62CurvatureVector F c0 t (sigma0.map x)) ∧
        (∀ x, curveVelocity (n := n) (fun s => v s (annulusPoint x 1)) 0 =
          m62CurvatureVector F c1 t (sigma1.map x)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ g' : RiemannianMetric n M,
          ∃ B : M64Annulus g' ((fun x => c0 x (t + s)) ∘ sigma0.map)
              ((fun x => c1 x (t + s)) ∘ sigma1.map),
            EqOn B.map (v s) m64AnnulusDomain ∧ B.area = m64AnnulusArea g' (v s)) ∧
        (∀ r : ℝ,
          let E := fun s p => m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p
          IntegrableOn (fun p => deriv (fun s => E s p) 0) m64AnnulusDomain volume ∧
            HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E s p)
              (∫ p in m64AnnulusDomain, deriv (fun s => E s p) 0) 0) ∧
        ∃ d : ℕ, ∃ h : LoopPlane → EuclideanSpace ℝ (Fin d),
          ContDiffOn ℝ 1 h m64AnnulusDomain ∧
          ∃ O : Set (EuclideanSpace ℝ (Fin d)), IsOpen O ∧ MapsTo h m64AnnulusDomain O ∧
            ∃ Phi : ℝ × EuclideanSpace ℝ (Fin d) → M,
              ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 d)) (𝓡 n) ∞ Phi
                (Ioo (-epsilon) epsilon ×ˢ O) ∧ v = fun s p => Phi (s, h p) := by
  obtain ⟨epsilon0, hepsilon0, htime0, L0, hL0, f0, hf0, hp0, htrace0, hvelocity0⟩ :=
    m64C2ShrinkingCurve_exists_finite_reference F hc0 ht sigma0 hsigma0
  obtain ⟨epsilon1, hepsilon1, -, L1, hL1, f1, hf1, hp1, htrace1, hvelocity1⟩ :=
    m64C2ShrinkingCurve_exists_finite_reference F hc1 ht sigma1 hsigma1
  let epsilon := min epsilon0 epsilon1
  have hepsilon : 0 < epsilon := lt_min hepsilon0 hepsilon1
  have hsmall0 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 := by
    intro s hs
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hsmall1 : Ioo (-epsilon) epsilon ⊆ Ioo (-epsilon1) epsilon1 := by
    intro s hs
    exact ⟨(neg_le_neg (min_le_right _ _)).trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hinit0 : f0 0 ∘ L0.map = (fun x => c0 x t) ∘ sigma0.map := by
    funext x
    simpa only [Function.comp_apply, add_zero] using htrace0 0 (hsmall0 hzero) x
  have hinit1 : f1 0 ∘ L1.map = (fun x => c1 x t) ∘ sigma1.map := by
    funext x
    simpa only [Function.comp_apply, add_zero] using htrace1 0 (hsmall1 hzero) x
  have hstart : ∃ B : M64Annulus (F.metric t) (f0 0 ∘ L0.map) (f1 0 ∘ L1.map),
      B.map = A.map := by
    rw [hinit0, hinit1]
    exact ⟨A, rfl⟩
  obtain ⟨A', hA'⟩ := hstart
  have hAreg : ContMDiffOn (𝓡 2) (𝓡 n) 1 A'.map m64AnnulusDomain := by
    rw [hA']
    exact hA
  obtain ⟨d, h, hh, delta, hdelta, O, hO, hmap, Phi, hPhi, hbase, hperiod,
      hlower, hupper, hfamily⟩ := m64Annulus_exists_finite_boundary_motion f0 f1 L0 L1
    hL0 hL1 A' hAreg hepsilon (hf0.mono (prod_mono_left hsmall0))
      (hf1.mono (prod_mono_left hsmall1)) hp0 hp1
  let eta := min delta epsilon
  have heta : 0 < eta := lt_min hdelta hepsilon
  have hdelta' : Ioo (-eta) eta ⊆ Ioo (-delta) delta := by
    intro s hs
    exact ⟨(neg_le_neg (min_le_left _ _)).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hepsilon' : Ioo (-eta) eta ⊆ Ioo (-epsilon) epsilon := by
    intro s hs
    exact ⟨(neg_le_neg (min_le_right _ _)).trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩
  have htime (s : ℝ) (hs : s ∈ Ioo (-eta) eta) : t + s ∈ Ioo a b :=
    htime0 s (hsmall0 (hepsilon' hs))
  let v := fun s p => Phi (s, h p)
  refine ⟨eta, heta, htime, v, ?_, hperiod, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hbase p).trans (congrFun hA' p)
  · intro s hs x
    exact (hlower s x).trans (htrace0 s (hsmall0 (hepsilon' hs)) x)
  · intro s hs x
    exact (hupper s x).trans (htrace1 s (hsmall1 (hepsilon' hs)) x)
  · intro x
    have heq : (fun s => v s (annulusPoint x 0)) = fun s => f0 s (L0.map x) :=
      funext fun s => hlower s x
    exact (congrArg (fun f : ℝ → M =>
      (curveVelocity (n := n) f 0 : EuclideanSpace ℝ (Fin n))) heq).trans (hvelocity0 x)
  · intro x
    have heq : (fun s => v s (annulusPoint x 1)) = fun s => f1 s (L1.map x) :=
      funext fun s => hupper s x
    exact (congrArg (fun f : ℝ → M =>
      (curveVelocity (n := n) f 0 : EuclideanSpace ℝ (Fin n))) heq).trans (hvelocity1 x)
  · intro s hs g'
    have hlo : f0 s ∘ L0.map = (fun x => c0 x (t + s)) ∘ sigma0.map :=
      funext fun x => htrace0 s (hsmall0 (hepsilon' hs)) x
    have hhi : f1 s ∘ L1.map = (fun x => c1 x (t + s)) ∘ sigma1.map :=
      funext fun x => htrace1 s (hsmall1 (hepsilon' hs)) x
    have hB := hfamily s (hdelta' hs) g'
    rw [hlo, hhi] at hB
    exact hB
  · intro r
    exact m64AnnulusMotionEnergy_hasDerivAt F t heta htime hO Phi
      (hPhi.mono (prod_mono_left hdelta')) r hh.contMDiffOn hmap
  · exact ⟨d, h, hh, O, hO, hmap, Phi, hPhi.mono (prod_mono_left hdelta'), rfl⟩

end PoincareConjecture
