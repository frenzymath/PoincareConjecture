import PoincareConjecture.Proofs.M47.LimitFiniteEndpointChartReadout
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointPhysicalMaps
import PoincareConjecture.Proofs.M34.Standard.SpatialJetConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoefficientTransport
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance endpointJetsDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointJetsDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance endpointJetsBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointJetsBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace



theorem limitFinite_endpoint_spatial_jets
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {T d R rho : ℝ} (hd : 0 < d) (hc : -T + d / 4 ≤ 0) (hrhoR : rho < R)
    (A : ℕ → RicciFlow 3 M (Icc (-(T + d / 2)) 0))
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (sigma eta : ℕ → ℕ) (heta : StrictMono eta) (B : ℝ × E → Bilin)
    (hB : ContDiffOn ℝ ∞ B (Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho))
    (hjets : ∀ r K, IsCompact K → K ⊆
      Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A (sigma k)).metric (p.1 + (-T + d / 4))).pullbackCoefficients Phi p.2))
        (iteratedFDeriv ℝ r B) atTop K) :
    ∀ r K, IsCompact K → K ⊆ Metric.ball 0 rho → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        (((A (sigma (eta k))).metric (-T)).pullbackCoefficients Phi))
      (iteratedFDeriv ℝ r (fun z => B (-d / 4, z))) atTop K := by
  let Omega := Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) rho
  let f := fun k (p : ℝ × E) =>
    ((A (sigma k)).metric (p.1 + (-T + d / 4))).pullbackCoefficients Phi p.2
  have hopen : IsOpen Omega := isOpen_Ioo.prod Metric.isOpen_ball
  have hsmooth (k : ℕ) : ContDiffOn ℝ ∞ (f k) Omega := by
    have hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 R) := by
      simpa only [hsource] using Phi.contMDiffOn
    apply (M44.contDiffOn_pullbackCoefficients_within (A (sigma k)) Metric.isOpen_ball hPhi).comp
      ((contDiffOn_fst.add contDiffOn_const).prodMk contDiffOn_snd)
    intro p hp
    refine ⟨⟨?_, ?_⟩, Metric.ball_subset_ball hrhoR.le hp.2⟩
    · linarith [hp.1.1]
    · linarith [hp.1.2]
  intro r K hK hKW
  let L := ({-d / 4} : Set ℝ) ×ˢ K
  have hLO : L ⊆ Omega := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hs' : s = -d / 4 := mem_singleton_iff.mp hs
    subst s
    exact ⟨⟨by linarith, by linarith⟩, hKW hz⟩
  have hL : IsCompact L := isCompact_singleton.prod hK
  have hspatial := M34.tendstoUniformlyOn_spatialJets_of_jointJets r
    (Filter.Eventually.of_forall fun k p hp =>
      (hsmooth k).contDiffAt (hopen.mem_nhds (hLO hp)))
    (fun p hp => hB.contDiffAt (hopen.mem_nhds (hLO hp))) (hjets r L hL hLO)
  have hslice := hspatial.comp (fun z : E => (-d / 4, z))
  have hpre : (fun z : E => (-d / 4, z)) ⁻¹' L = K := by ext z; simp [L]
  rw [hpre] at hslice
  have hclock : -d / 4 + (-T + d / 4) = -T := by ring
  have hconv : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r (((A (sigma k)).metric (-T)).pullbackCoefficients Phi))
      (iteratedFDeriv ℝ r (fun z => B (-d / 4, z))) atTop K := by
    simpa only [Function.comp_def, f, hclock] using hslice
  intro V hV
  exact heta.tendsto_atTop.eventually (hconv V hV)




theorem limitFinite_endpoint_physical_jet_readout
    {C : GeneralizedSliceCarrier.{u}} (F : ℕ → SurgeryFlowData.{u})
    (base Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (U : TopologicalSpace.Opens C.carrier)
    {T d R rho : ℝ} (hd : 0 < d) (hc : -T + d / 4 ≤ 0) (hrhoR : rho < R)
    (A : ℕ → RicciFlow 3 U (Icc (-(T + d / 2)) 0))
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (sigma eta : ℕ → ℕ) (heta : StrictMono eta)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      ((F k).slice (base k + -T / Q k)).carrier ∞)
    (hphysical : ∀ᶠ k in atTop, ∃ b, ∃ ht : -T ∈ Icc b 0,
      ∃ e : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc b 0) U,
        EqOn (psi k) (e.forward (-T) ht) U ∧
        ∀ (x : U) (v w : E), ((A (sigma (eta k))).metric (-T)).inner x v w =
          e.pullbackInner (-T) ht x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (B : ℝ × E → Bilin)
    (hB : ContDiffOn ℝ ∞ B (Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho))
    (hjets : ∀ r K, IsCompact K → K ⊆
      Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A (sigma k)).metric (p.1 + (-T + d / 4))).pullbackCoefficients Phi p.2))
        (iteratedFDeriv ℝ r B) atTop K)
    (gE : RiemannianMetric 3 C.carrier)
    (hendpoint : EqOn (fun z => B (-d / 4, z))
      (gE.pullbackCoefficients (fun z : E => (Phi z).val)) (Metric.ball 0 rho)) :
    ∀ r K, IsCompact K → K ⊆ Metric.ball 0 rho → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        ((rescaledMetric ((F k).metric (base k + -T / Q k)) (Q k) (hQ k)).pullbackCoefficients
          (psi k ∘ (fun z : E => (Phi z).val))))
      (iteratedFDeriv ℝ r (gE.pullbackCoefficients (fun z : E => (Phi z).val))) atTop K := by
  have hcoeff : ∀ᶠ k in atTop, EqOn
      ((rescaledMetric ((F k).metric (base k + -T / Q k)) (Q k) (hQ k)).pullbackCoefficients
        (psi k ∘ (fun z : E => (Phi z).val)))
      (((A (sigma (eta k))).metric (-T)).pullbackCoefficients Phi) (Metric.ball 0 rho) := by
    filter_upwards [hphysical] with k hk
    obtain ⟨b, ht, e, hmap, hmetric⟩ := hk
    intro z hz
    have hzPhi : z ∈ Phi.source := by
      rw [hsource]
      exact Metric.ball_subset_ball hrhoR.le hz
    let f : U → ((F k).slice (base k + -T / Q k)).carrier :=
      fun x => e.forward (-T) ht x.val
    have hsub := (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U).mdifferentiable
      (by simp) (Phi z)
    have hforward := (M44.cylinderSliceChart e U.isOpen (-T) ht).mdifferentiableAt
      (by simp) (Phi z).property
    have hf : MDifferentiableAt (𝓡 3) (𝓡 3) f (Phi z) := hforward.comp (Phi z) hsub
    have hgerm : (psi k ∘ (fun z : E => (Phi z).val)) =ᶠ[𝓝 z] f ∘ Phi :=
      Filter.Eventually.of_forall fun y => hmap (Phi y).property
    apply M44.pullbackCoefficients_eq_of_metric_germ
      ((A (sigma (eta k))).metric (-T))
      (rescaledMetric ((F k).metric (base k + -T / Q k)) (Q k) (hQ k))
      hf (Phi.mdifferentiableAt (by simp) hzPhi) hgerm
    intro v w
    have hdif := mfderiv_comp (Phi z) hforward hsub
    change mfderiv (𝓡 3) (𝓡 3) f (Phi z) =
      (mfderiv (𝓡 3) (𝓡 3) (e.forward (-T) ht) (Phi z).val).comp
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi z)) at hdif
    have hread := hmetric (Phi z) v w
    dsimp [SurgeryFlowCylinder.pullbackInner] at hread
    change Q k * ((F k).metric (base k + -T / Q k)).inner (f (Phi z))
      (mfderiv (𝓡 3) (𝓡 3) f (Phi z) v)
      (mfderiv (𝓡 3) (𝓡 3) f (Phi z) w) = _
    rw [hdif]
    exact hread.symm
  intro r K hK hKW
  have hconv := limitFinite_endpoint_spatial_jets hd hc hrhoR A Phi hsource
    sigma eta heta B hB hjets r K hK hKW
  apply (hconv.congr_right
    ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
      Metric.isOpen_ball hendpoint r).mono hKW)).congr
  filter_upwards [hcoeff] with k hk
  exact ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
    Metric.isOpen_ball hk r).mono hKW).symm

end PoincareConjecture.M47
