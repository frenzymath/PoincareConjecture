import PoincareConjecture.Proofs.M47.TerminalCurvaturePinchedChartBound
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierReadout











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance actualBoundDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance actualBoundDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance actualBoundBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance actualBoundBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section OriginalCharts

variable {ι : Type*} (U : ι → Opens E) [∀ i, Nonempty (U i)]

private noncomputable local instance actualOriginalChartSpace (i : ι) :
    ChartedSpace E (U i) :=
  (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace

private noncomputable local instance actualOriginalChartManifold (i : ι) :
    IsManifold (𝓡 3) ∞ (U i) :=
  (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)




theorem terminalCurvature_bound_of_actual_sources
    (sched : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} sched.setup.C)
    (pfx : SurgeryParameterPrefix sched.constants) (P : M46Predecessors.{u})
    (S : ℕ → SurgeryFlowData.{u}) (base Q r : ℕ → ℝ)
    (hQ : Tendsto Q atTop atTop) (sigma : ℕ → ℕ) (hsigma : StrictMono sigma)
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (G : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
    (coeff : ι → ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (hcoeff : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ (x : U i) v w,
      ((G i).metric t).inner x v w = coeff i (t, x) v w)
    (O : ∀ (_i : ι) (k : ℕ), SurgeryObservation (S k))
    (W : ∀ (_i : ι) (k : ℕ), M33RegularHistoryWindow (S k))
    (H : ∀ i k, M33RegularHistoryData (W i k))
    (C : ι → ℕ → GeneralizedSliceCarrier.{u})
    (V : ∀ i k, Opens (C i k).carrier)
    (e : ∀ i k, GeneralizedFlowCylinder (H i k).generalized (C i k)
      (base k) (Q k) (Icc (-tau i) 0) (V i k))
    (F : ∀ i k, RicciFlow 3 (V i k) (Icc (-tau i) 0))
    (R L eta : ι → ℝ)
    (normal : ∀ i k, TerminalSourceChart ((F i k).metric 0) (R i))
    (hGood : ∀ i, ∀ᶠ k in atTop, TerminalSourceJetsG4Good sched B pfx (O i k) (H i k)
      (V i k) (e i k) (F i k) (L := L i) (eta := eta i) (rNext := r k) (normal i k))
    (hmetric : ∀ i k (s : ℝ) (hs : s ∈ Icc (-tau i) 0) (x : V i k),
      ∀ v w : TangentSpace (𝓡 3) x,
        ((F i k).metric s).inner x v w = (e i k).pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V i k → (C i k).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V i k → (C i k).carrier) x w))
    (phi : ∀ i k, U i → V i k)
    (hphi : ∀ i k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (phi i k))
    (hjet : ∀ i m K, IsCompact K → K ⊆ Ioo (-tau i) 0 ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun z : ℝ × E =>
        ((F i (sigma k)).metric z.1).pullbackCoefficients
          (ChartDistance.chartParametrization (fun j => (U j : Set E))
            (fun j => (U j).isOpen) (phi i (sigma k))) z.2))
      (iteratedFDeriv ℝ m (coeff i)) atTop K)
    {X : Type u} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [T3Space X]
    [SecondCountableTopology X] [ConnectedSpace X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (p : X) (hscalar : D.scalarCurvature p ≠ 0)
    (q : ∀ i, U i → X)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : U i) (y : U j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 3) x) (c d : TangentSpace (𝓡 3) y),
        mfderiv (𝓡 3) (𝓡 3) (q i) x a = mfderiv (𝓡 3) (𝓡 3) (q j) y c →
        mfderiv (𝓡 3) (𝓡 3) (q i) x b = mfderiv (𝓡 3) (𝓡 3) (q j) y d →
        ((G i).metric t).inner x a b = ((G j).metric t).inner y c d)
    (hterminal : ∀ i (x : U i) (a b : TangentSpace (𝓡 3) x),
      ((G i).metric 0).inner x a b = g.inner (q i x)
        (mfderiv (𝓡 3) (𝓡 3) (q i) x a) (mfderiv (𝓡 3) (𝓡 3) (q i) x b))
    (exh : ℕ → Set X) (hopen : ∀ j, IsOpen (exh j))
    (hconnected : ∀ j, IsConnected (exh j))
    (hcompact : ∀ j, IsCompact (closure (exh j)))
    (hnested : ∀ j, closure (exh j) ⊆ exh (j + 1))
    (hexhaust : (⋃ j, exh j) = univ) (hp : ∀ j, p ∈ exh j)
    (Cphysical : ℕ → GeneralizedSliceCarrier.{u})
    (duration : ℕ → ℝ) (hduration : ∀ k, 0 < duration k)
    (Vphysical : ∀ k, Opens (Cphysical k).carrier) (qphysical : ∀ k, Vphysical k)
    (ephysical : ∀ k, SurgeryFlowCylinder (S k) (Cphysical k) (base k) (Q k)
      (Icc (-duration k) 0) (Vphysical k))
    (Fphysical : ∀ k, RicciFlow 3 (Vphysical k) (Icc (-duration k) 0))
    (hphysical : ∀ k (s : ℝ) (hs : s ∈ Icc (-duration k) 0) (y : Vphysical k)
      (v w : TangentSpace (𝓡 3) y),
      ((Fphysical k).metric s).inner y v w = (ephysical k).pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Vphysical k → (Cphysical k).carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Vphysical k → (Cphysical k).carrier) y w))
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (Vphysical (sigma k)) ∞)
    (hsource : ∀ k, (psi k).source = exh k)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hterminalJet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((Fphysical (sigma k)).metric 0).pullbackCoefficients (psi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K)
    (hfloor : ∀ k, (r k)⁻¹ ^ 2 ≤ Q k)
    (hEpsilon : ∀ k, (S k).parameters.epsilon = sched.setup.epsilon)
    (hC : ∀ k, (S k).parameters.C = sched.setup.C)
    (hPast : ∀ k, SurgeryCanonicalOn (S k) (Ico 0 (base k)) (r k)) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ x : X, D.curvatureTensorNorm x ≤ B0 := by
  have hmono : Monotone exh := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnested j)
  have hreadout := terminalCurvature_high_point_readout_of_source_cylinders sched
    (fun k => S (sigma k)) (fun k => Cphysical (sigma k))
    (fun k => base (sigma k)) (fun k => Q (sigma k))
    (fun k => duration (sigma k)) (fun k => r (sigma k))
    (fun k => hduration (sigma k)) (fun k => Vphysical (sigma k))
    (fun k => qphysical (sigma k)) (fun k => ephysical (sigma k))
    (fun k => Fphysical (sigma k)) (fun k => hphysical (sigma k))
    g D hcomplete exh hopen hmono hexhaust hcompact p hp psi hsource c hcoverC
    hterminalJet (fun k => hfloor (sigma k)) (fun k => hEpsilon (sigma k))
    (fun k => hC (sigma k)) (fun k => hPast (sigma k))
  have hhalf : sched.setup.epsilon ≤ sched.calibration.epsilon₁ / 2 :=
    sched.calibration.epsilon_source_le.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmall : 2 * sched.setup.epsilon ≤ sched.calibration.epsilon₁ := by linarith
  have hcalibrated : 2 * sched.setup.epsilon ≤ 1 / 200 :=
    sched.calibration.two_epsilon_le_bounded_distance.trans sched.calibration.epsilon₁₀_le
  have hepsilon : 0 < 2 * sched.setup.epsilon := mul_pos (by norm_num) sched.setup.epsilon_pos
  have hA : 0 < 4 * max 1 sched.setup.C := by positivity
  exact terminalCurvature_bound_of_pinched_original_charts U sched B pfx P tau htau G
    coeff hcoeff (fun _ => S) O W H C (fun _ => base) (fun _ => Q) (fun _ => r)
    V e F R L eta normal hGood hmetric (fun _ => hQ) phi hphi sigma hsigma hjet
    sched.calibration.small_neck_scale_bound hepsilon hsmall hcalibrated hA
    D hcomplete p hscalar q hq hcover hinv hterminal exh hopen hconnected hcompact
    hnested hexhaust hreadout

end OriginalCharts

end PoincareConjecture.M47
