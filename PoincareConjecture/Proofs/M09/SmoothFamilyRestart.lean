import PoincareConjecture.Proofs.M09.SmoothFamilyDomain
import PoincareConjecture.Proofs.M09.FamilyPhase
import PoincareConjecture.Proofs.M09.SmoothTangentChartPhase
import PoincareConjecture.Proofs.M09.ForwardRegularizedContinuation

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => ℝ × (V × V)

set_option backward.isDefEq.respectTransparency false in
theorem normalizedSquareFamily_mem_smoothFamilyDomain_of_restart {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - b) T))
    (p0 p : M) (z0 : Q) (A : LocalRegularizedRestartFamily F T b p z0)
    (Z0 : TangentSpace (𝓡 n) p0) (r t : ℝ) (hr : r ∈ Set.Ico 0 (Real.sqrt b))
    (ht : 0 < t) (hrt : t ∈ Set.Ioo (r - A.radius) (r + A.radius))
    (hchart : normalizedSquareFamily F T b p0 Z0 r ∈ (chartAt V p).source)
    (hparam : (r, tangentChartPhase p
      (curvePhase (n := n) (normalizedSquareFamily F T b p0 Z0) r)) ∈ A.neighborhood) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    (Z0, r) ∈ smoothFamilyDomain (n := n)
      (fun z ↦ normalizedSquareFamily F T b p0 z.1 z.2) →
    (Z0, t) ∈ smoothFamilyDomain (n := n)
      (fun z ↦ normalizedSquareFamily F T b p0 z.1 z.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  intro hstart
  let E := TangentSpace (𝓡 n) p0
  let f : E × ℝ → M := fun z ↦ normalizedSquareFamily F T b p0 z.1 z.2
  obtain ⟨U, hU, hZU, hf⟩ := hstart
  let i : E → E × ℝ := fun Z ↦ (Z, r)
  let q : E → TangentBundle (𝓡 n) M := fun Z ↦ familyPhase (n := n) f (i Z)
  let W0 : Set E := i ⁻¹' U
  have hi : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E × ℝ)) ∞ i :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have hW0 : IsOpen W0 := hU.preimage hi.continuous
  have hq : ContMDiffOn (𝓘(ℝ, E)) ((𝓡 n).prod (𝓡 n)) ∞ q W0 :=
    (familyPhase_contMDiffOn f U hU hf).comp hi.contMDiffOn (fun _ hZ ↦ hZ)
  have hbase : ContMDiffOn (𝓘(ℝ, E)) (𝓡 n) ∞ (fun Z ↦ f (Z, r)) W0 :=
    hf.comp hi.contMDiffOn (fun _ hZ ↦ hZ)
  let W1 := W0 ∩ (fun Z : E ↦ f (Z, r)) ⁻¹' (chartAt V p).source
  have hW1 : IsOpen W1 :=
    hbase.continuousOn.isOpen_inter_preimage hW0 (chartAt V p).open_source
  have hcoord : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, V × V)) ∞
      (fun Z ↦ tangentChartPhase p (q Z)) W1 :=
    (tangentChartPhase_contMDiffOn p).comp (hq.mono Set.inter_subset_left)
      (fun Z hZ ↦ hZ.2)
  let psi : E → Q := fun Z ↦ (r, tangentChartPhase p (q Z))
  have hpsi : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, Q)) ∞ psi W1 :=
    (contMDiffOn_prod_module_iff psi).mpr ⟨contMDiffOn_const, hcoord⟩
  let W := W1 ∩ psi ⁻¹' A.neighborhood
  have hW : IsOpen W := hpsi.continuousOn.isOpen_inter_preimage hW1 A.neighborhood_open
  have hZ0 : Z0 ∈ W := ⟨⟨hZU, hchart⟩, hparam⟩
  let L := Set.Ioo (r - A.radius) (r + A.radius)
  let I := L ∩ Set.Ioi 0
  have hI : IsOpen I := isOpen_Ioo.inter isOpen_Ioi
  have hrL : r ∈ L := ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩
  have hpsiW := hpsi.mono (show W ⊆ W1 from Set.inter_subset_left)
  have hfst : ContMDiff (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, E)) ∞ Prod.fst :=
    contDiff_fst.contMDiff
  have hsnd : ContMDiff (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, ℝ)) ∞ Prod.snd :=
    contDiff_snd.contMDiff
  have hmap : ContMDiffOn (𝓘(ℝ, E × ℝ)) ((𝓘(ℝ, Q)).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : E × ℝ ↦ (psi z.1, z.2)) (W ×ˢ I) :=
    (hpsiW.comp hfst.contMDiffOn (fun z hz ↦ hz.1)).prodMk hsnd.contMDiffOn
  have hH : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z : E × ℝ ↦ A.curve (psi z.1) z.2) (W ×ˢ I) := by
    apply A.curve_smooth.comp hmap
    intro z hz
    refine ⟨hz.1.2, ?_, ?_⟩
    · change -A.radius < z.2 - r
      linarith [hz.2.1.1]
    · change z.2 - r < A.radius
      linarith [hz.2.1.2]
  have heq : Set.EqOn f (fun z : E × ℝ ↦ A.curve (psi z.1) z.2) (W ×ˢ I) := by
    rintro ⟨Z, s⟩ ⟨hZ, hs⟩
    let q0 : TangentBundle (𝓡 n) M := ⟨p0, (2 : ℝ) • Z⟩
    let S := maximalRegularizedSolution F hM04 T b hb hwindow 0
      ⟨neg_lt_zero.mpr (Real.sqrt_pos.mpr hb), Real.sqrt_pos.mpr hb⟩ q0
    have hforward : Set.Ico 0 (Real.sqrt b) ⊆ S.domain :=
      Ico_subset_maximalRegularizedDomain F hM04 T b hb hwindow hcurvature q0
    have hlocal := A.isLocalRegularizedCurveOn hM04 hb hwindow (psi Z) hZ.2
    have hphase : curvePhase (n := n) S.curve r =
        curvePhase (n := n) (A.curve (psi Z)) r := by
      have hA := A.initial_phase (psi Z) hZ.2
      change curvePhase (n := n) (A.curve (psi Z)) r =
        (⟨(chartAt V p).symm (tangentChartPhase p (q Z)).1,
          (mfderiv (𝓡 n) (𝓡 n) (chartAt V p).symm (tangentChartPhase p (q Z)).1)
            (tangentChartPhase p (q Z)).2⟩ : TangentBundle (𝓡 n) M) at hA
      exact (hA.trans (tangentChartPhase_inverse p (q Z) hZ.1.2)).symm
    have huniq := localRegularizedCurve_phase_eqOn F hM04 T b hb hwindow
      S.curve (A.curve (psi Z)) (S.domain ∩ L) (S.open_domain.inter isOpen_Ioo)
      (S.preconnected_domain.ordConnected.inter Set.ordConnected_Ioo).isPreconnected
      (fun _ h ↦ S.time_mem h.1) (S.isLocal.mono Set.inter_subset_left)
      (hlocal.mono Set.inter_subset_right) r ⟨hforward hr, hrL⟩ hphase
    have hstime : s < Real.sqrt b := (A.time_mem (psi Z) hZ.2 s hs.1).2
    exact congrArg Bundle.TotalSpace.proj (huniq ⟨hforward ⟨hs.2.le, hstime⟩, hs.1⟩)
  exact ⟨W ×ˢ I, hW.prod hI, ⟨hZ0, hrt, ht⟩, hH.congr heq⟩

end PoincareConjecture.Proofs.M09
