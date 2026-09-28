import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionEnergyTrace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {k : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin k)) N] [IsManifold (𝓡 k) ∞ N]
  {a b : ℝ}

omit [IsManifold (𝓡 n) ∞ M] in

theorem m64AnnulusMotionEnergyTrace_ae_eq (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O))
    (r : ℝ) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hfO : MapsTo f m64AnnulusDomain O) {s : ℝ} (hs : s ∈ T) :
    (fun p => m64AnnulusMotionEnergyTrace (n := n) F time Phi r f (s, p))
      =ᵐ[volume.restrict m64AnnulusDomain]
        m64ModulusEnergyDensity (F.metric (time + s)) r (fun p => Phi (s, f p)) := by
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  exact m64AnnulusMotionEnergyTrace_eq F time hT hO Phi hPhi r hf hfO hs hp

theorem m64AnnulusMotionEnergy_integrable (F : RicciFlow k N (Icc a b))
    (time : ℝ) {T : Set ℝ} (hT : IsOpen T) {O : Set M} (hO : IsOpen O)
    (hTF : ∀ s ∈ T, time + s ∈ Ioo a b) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi (T ×ˢ O))
    (r : ℝ) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hfO : MapsTo f m64AnnulusDomain O) {s : ℝ} (hs : s ∈ T) :
    IntegrableOn (m64ModulusEnergyDensity (F.metric (time + s)) r
      (fun p => Phi (s, f p))) m64AnnulusDomain volume := by
  have hE := (m64AnnulusMotionEnergyTrace_continuous F time hT hO hTF Phi hPhi r hf hfO).1
  have hc : ContinuousOn (fun p => m64AnnulusMotionEnergyTrace (n := n) F time Phi r f (s, p))
      m64AnnulusDomain :=
    hE.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hp => ⟨hs, hp⟩)
  exact (hc.integrableOn_compact m64AnnulusDomain_isCompact).congr
    (m64AnnulusMotionEnergyTrace_ae_eq F time hT hO Phi hPhi r hf hfO hs)

theorem m64AnnulusMotionEnergy_hasDerivAt (F : RicciFlow k N (Icc a b))
    (time : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hTF : ∀ s ∈ Ioo (-epsilon) epsilon, time + s ∈ Ioo a b)
    {O : Set M} (hO : IsOpen O) (Phi : ℝ × M → N)
    (hPhi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 k) ∞ Phi
      (Ioo (-epsilon) epsilon ×ˢ O))
    (r : ℝ) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (hfO : MapsTo f m64AnnulusDomain O) :
    let E := fun s p => m64ModulusEnergyDensity (F.metric (time + s)) r
      (fun z => Phi (s, f z)) p
    IntegrableOn (fun p => deriv (fun s => E s p) 0) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E s p)
        (∫ p in m64AnnulusDomain, deriv (fun s => E s p) 0) 0 := by
  let E := fun s p => m64ModulusEnergyDensity (F.metric (time + s)) r
    (fun z => Phi (s, f z)) p
  let H := m64AnnulusMotionEnergyTrace (n := n) F time Phi r f
  let H' := m64AnnulusMotionEnergyDerivativeTrace (n := n) F time Phi r f
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  obtain ⟨hE, hD⟩ := m64AnnulusMotionEnergyTrace_continuous F time isOpen_Ioo hO hTF
    Phi hPhi r hf hfO
  obtain ⟨hI, hder⟩ := m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    (F := fun s p => H (s, p)) (F' := fun s p => H' (s, p)) hepsilon
    (fun s hs => hE.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hp => ⟨hs, hp⟩)) hD
    (fun s hs p hp => m64AnnulusMotionEnergyTrace_hasDerivAt F time isOpen_Ioo hO hTF
      Phi hPhi r f hs p (hfO hp))
  have hjet : (fun p => H' (0, p)) =ᵐ[volume.restrict m64AnnulusDomain]
      fun p => deriv (fun s => E s p) 0 := by
    rw [m64Annulus_restrict_closed_eq_interior]
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    have hd : HasDerivAt (fun s => E s p) (H' (0, p)) 0 := by
      apply (m64AnnulusMotionEnergyTrace_hasDerivAt F time isOpen_Ioo hO hTF
        Phi hPhi r f hzero p (hfO (interior_subset hp))).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact (m64AnnulusMotionEnergyTrace_eq F time isOpen_Ioo hO Phi hPhi r hf hfO hs hp).symm
    exact hd.deriv.symm
  refine ⟨hI.congr hjet, ?_⟩
  apply (hder.congr_deriv (integral_congr_ae hjet)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  exact (integral_congr_ae
    (m64AnnulusMotionEnergyTrace_ae_eq F time isOpen_Ioo hO Phi hPhi r hf hfO hs)).symm

end PoincareConjecture
